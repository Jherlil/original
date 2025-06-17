#include "rmd160_bsgs.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <string.h>
#include <vector>
#include <array>
#include <unordered_set>
#include <getopt.h>
#include <chrono>
#include <thread>
#include <omp.h>

#include "base58/libbase58.h"
#include "hash/sha256.h"
#include "hash/ripemd160.h"
#include "secp256k1/SECP256k1.h"
#include "secp256k1/Point.h"
#include "secp256k1/Int.h"
#include "util.h"

struct RmdEntry {
    uint8_t hash[20];
    uint8_t priv[32];
};

static uint8_t byte_encode_crypto = 0x00;

static void rmd160toaddress_dst(uint8_t *rmd, char *dst){
    char digest[60];
    size_t sz = 40;
    digest[0] = byte_encode_crypto;
    memcpy(digest + 1, rmd, 20);
    sha256((uint8_t*)digest, 21, (uint8_t*)digest + 21);
    sha256((uint8_t*)digest + 21, 32, (uint8_t*)digest + 21);
    if(!b58enc(dst,&sz,digest,25)){
        fprintf(stderr,"error b58enc\n");
    }
}

static void privkey_to_wif_dst(uint8_t *priv, bool compressed, char *dst){
    uint8_t tmp[38];
    uint8_t hash[32];
    size_t off = 0;
    tmp[off++] = 0x80;
    memcpy(tmp + off, priv, 32);
    off += 32;
    if(compressed){
        tmp[off++] = 0x01;
    }
    sha256(tmp, off, hash);
    sha256(hash, 32, hash);
    memcpy(tmp + off, hash, 4);
    size_t sz = 60;
    if(!b58enc(dst, &sz, tmp, off + 4)){
        fprintf(stderr, "error b58enc wif\n");
    }
}

struct Hash20Arr {
    std::array<uint8_t,20> h;
    bool operator==(const Hash20Arr &o) const noexcept {
        return memcmp(h.data(), o.h.data(), 20) == 0;
    }
};

struct Hash20Hasher {
    size_t operator()(const Hash20Arr &a) const noexcept {
        const uint64_t *p = reinterpret_cast<const uint64_t*>(a.h.data());
        size_t v = p[0] ^ p[1];
        v ^= ((size_t)a.h[16] << 24) | ((size_t)a.h[17] << 16) | ((size_t)a.h[18] << 8) | a.h[19];
        return v;
    }
};

typedef std::unordered_set<Hash20Arr, Hash20Hasher> TargetSet;

static bool load_targets(const char *fname, TargetSet &out){
    FILE *f = fopen(fname,"r");
    if(!f){
        fprintf(stderr,"[E] Cannot open %s\n", fname);
        return false;
    }
    char line[1024];
    while(fgets(line,sizeof(line),f)){
        trim(line," \t\n\r");
        size_t len = strlen(line);
        if(len==0) continue;
        if(len==40 && isValidHex(line)){
            unsigned char buf[20];
            hexs2bin(line, buf);
            Hash20Arr t; memcpy(t.h.data(), buf, 20);
            out.insert(t);
        }
    }
    fclose(f);
    return true;
}

// Generate a block of keys and their hash160 sequentially
static void generate_block_serial(Secp256K1 &secp, Int *start, uint64_t count, RmdEntry *table){
    Int key; key.Set(start);
    Point pub = secp.ComputePublicKey(&key);

    uint64_t i=0;
    while(i+4 <= count){
        Point p0 = pub;
        Point p1 = secp.AddDirect(p0,secp.G);
        Point p2 = secp.AddDirect(p1,secp.G);
        Point p3 = secp.AddDirect(p2,secp.G);
        secp.GetHash160(P2PKH,true,
            p0,p1,p2,p3,
            table[i].hash,
            table[i+1].hash,
            table[i+2].hash,
            table[i+3].hash);
        key.Get32Bytes(table[i].priv); key.AddOne();
        key.Get32Bytes(table[i+1].priv); key.AddOne();
        key.Get32Bytes(table[i+2].priv); key.AddOne();
        key.Get32Bytes(table[i+3].priv); key.AddOne();
        pub = secp.AddDirect(p3,secp.G);
        i+=4;
    }
    for(; i<count; ++i){
        secp.GetHash160(P2PKH,true,pub,table[i].hash);
        key.Get32Bytes(table[i].priv);
        key.AddOne();
        pub = secp.AddDirect(pub,secp.G);
    }
}

// Thread worker to generate a slice of the table
static void generate_block_slice(Int base, uint64_t count, RmdEntry *table){
    Secp256K1 secp; secp.Init();
    generate_block_serial(secp,&base,count,table);
}

// Parallel generation using OpenMP threads
static void generate_block_parallel(Int *start, uint64_t count, RmdEntry *table, int threads){
    uint64_t chunk = count / threads;
    #pragma omp parallel for schedule(static) num_threads(threads)
    for(int t=0; t<threads; ++t){
        uint64_t begin = (uint64_t)t * chunk;
        uint64_t len = (t==threads-1) ? (count - begin) : chunk;
        Int key; key.Set(start); key.Add(begin);
        generate_block_slice(key, len, table + begin);
    }
}

static void compare_block(const TargetSet &targets, RmdEntry *table, uint64_t count, int threads){
#pragma omp parallel for schedule(static) num_threads(threads)
    for(uint64_t i=0;i<count;i++){
        Hash20Arr t; memcpy(t.h.data(), table[i].hash, 20);
        if(targets.find(t)!=targets.end()){
            Int key; key.Set32Bytes(table[i].priv);
            char *hex = key.GetBase16();
            char addr[50] = {0};
            char wif[60] = {0};
            rmd160toaddress_dst(table[i].hash, addr);
            privkey_to_wif_dst(table[i].priv, true, wif);
#pragma omp critical
            {
                printf("[+] HIT privkey %s WIF %s address %s\n", hex, wif, addr);
            }
            free(hex);
        }
    }
}

int rmd160_bsgs_main(int argc, char **argv){
    uint32_t kbits = 20;
    const char *file = NULL;
    int threads = 2;
    const char *start_str = "1";
    bool show_stats = false;

    static struct option long_options[] = {
        {"stats", no_argument, 0, 0},
        {0,0,0,0}
    };

    int opt; int long_idx=0;
    while((opt = getopt_long(argc,argv,"k:f:t:r:",long_options,&long_idx))!= -1){
        if(opt==0){
            show_stats = true; continue;
        }
        switch(opt){
            case 'k': kbits = strtoul(optarg,NULL,10); break;
            case 'f': file = optarg; break;
            case 't': threads = atoi(optarg); break;
            case 'r': start_str = optarg; break;
            default: fprintf(stderr,"usage: rmd160-bsgs -k N -f file -t N -r start [--stats]\n"); return 0;
        }
    }
    if(!file){
        fprintf(stderr,"[E] target file required with -f\n");
        return 1;
    }
    if(threads<2 || (threads%2)!=0){
        fprintf(stderr,"[E] -t threads must be >=2 and even\n");
        return 1;
    }

    TargetSet targets;
    if(!load_targets(file, targets)) return 1;

    uint64_t table_size = 1ULL<<kbits;
    printf("[+] Table 2^%u (%" PRIu64 ") entries\n", kbits, table_size);

    RmdEntry *table0 = (RmdEntry*)malloc(sizeof(RmdEntry)*table_size);
    RmdEntry *table1 = (RmdEntry*)malloc(sizeof(RmdEntry)*table_size);
    if(!table0 || !table1){
        fprintf(stderr,"[E] malloc table\n");
        return 1;
    }

    Int current; if(strncmp(start_str,"0x",2)==0 || strncmp(start_str,"0X",2)==0) current.SetBase16(start_str+2); else current.SetBase10(start_str);
    Int step; step.SetInt64(table_size);

    // Precompute first block to start the pipeline
    generate_block_parallel(&current, table_size, table0, threads/2);
    current.Add(&step);

    uint64_t total=0; int idx=0;
    auto last = std::chrono::steady_clock::now();
    while(true){
        int next = idx ^ 1;
        Int next_start; next_start.Set(&current);
        std::thread gen_thr(generate_block_parallel, &next_start, table_size, next?table1:table0, threads/2);
        current.Add(&step);

        compare_block(targets, idx?table1:table0, table_size, threads/2);
        gen_thr.join();

        total += table_size;
        idx = next;

        if(show_stats){
            auto now = std::chrono::steady_clock::now();
            double sec = std::chrono::duration<double>(now-last).count();
            if(sec>=1.0){
                double speed = (double)total/sec;
                printf("[+] %" PRIu64 " keys in %.2f sec : %.2f keys/s\n", total, sec, speed);
                last = now;
                total = 0;
            }
        }
    }

    free(table0); free(table1);
    return 0;
}

#ifdef STANDALONE
int main(int argc, char **argv){
    return rmd160_bsgs_main(argc, argv);
}
#endif

