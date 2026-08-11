
// holdem_5player_169hands_cpuonly_evalfix_mit_production_checkpoint.cpp
//
// CPU-only exact board-first Hold'em enumerator for one fixed hero hand against random
// opponent hands, optimized for one large target player count, fixed at 5 total players, checkpoint-resumable over a requested hand-index range, with a specialized 5-player meet-in-the-middle counter and production progress/ETA logging.
//
// This is the third-generation board-first version optimized for speed while capping the per-hand board-signature cache:
//   * CPU evaluates, for each board, the hero hand and all C(45,2)=990
//     possible opponent hands exactly once.
//   * The host then performs exact disjoint-hand matching counting by compressing
//     the board's 45 remaining cards into exact edge-rank-equivalent card types.
//   * A memoized histogram dynamic program counts ordered opponent-seat assignments
//     from those card-type capacities. The DP state does not include current-best
//     rank; instead it returns a top-rank/tie-count histogram. It does not enumerate every complete 5-player
//     deal.
//
// IMPORTANT:
// This is exact. It is also a serious prototype of the optimized matching
// counter. Its speed depends on how much exact type compression the board allows.
// Boards that cannot be compressed enough will still be expensive. The program
// reports the maximum and average number of exact card types encountered.
//
// Input:
// Input:
//   executable <p1> <p2> <checkpoint_file> <output_csv> [chunk_boards]
//
// Example:
//   executable 0 168 run5p.chk results_5p.csv
//
// HandRanks.dat must be in the current directory.

#include <algorithm>
#include <array>
#include <atomic>
#include <csignal>
#include <ctime>
#include <cctype>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <thread>
#include <mutex>
#include <iostream>
#include <limits>
#include <numeric>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#if defined(_WIN32)
#ifndef NOMINMAX
#define NOMINMAX
#endif
#include <windows.h>
#else
#include <sys/resource.h>
#include <unistd.h>
#endif


#ifndef DEFAULT_CHUNK_BOARDS
#define DEFAULT_CHUNK_BOARDS 16
#endif

#ifndef PROGRAM_VARIANT_NAME
#define PROGRAM_VARIANT_NAME "cpuonly_5player_169hands_evalfix_mit_production"
#endif


#ifndef CHECKPOINT_INTERVAL_SECONDS
#define CHECKPOINT_INTERVAL_SECONDS 3600.0
#endif

#ifndef DEFAULT_MIT_CPU_WORKER_THREADS
#define DEFAULT_MIT_CPU_WORKER_THREADS 1
#endif

#ifndef DEFAULT_BOARD_CACHE_LIMIT
#define DEFAULT_BOARD_CACHE_LIMIT 0
#endif

static constexpr int EDGE_COUNT = 990; // C(45,2)
static constexpr int CATEGORY_COUNT = 80;
static constexpr int HR_EXPECTED_SIZE = 32487834;

// Category layout for total players p = 2..9:
//
// base[p] + 0                       hero strict win
// base[p] + 1..p-1                  hero tie size 2..p
// base[p] + p                       opponent strict winner, hero loses
// base[p] + p+1..p+(p-2)            opponent-only tie size 2..p-1
static constexpr int HOST_CAT_BASE[10] = {
    0, 0, 0, 3, 8, 15, 24, 35, 48, 63
};


struct U128 {
    unsigned long long lo;
    unsigned long long hi;
};

static inline U128 u128_zero() { return U128{0ULL, 0ULL}; }
static inline U128 u128_from_u64(unsigned long long x) { return U128{x, 0ULL}; }

static inline void u128_add_inplace(U128& a, const U128& b) {
    const unsigned long long old = a.lo;
    a.lo += b.lo;
    a.hi += b.hi + (a.lo < old ? 1ULL : 0ULL);
}

// MSVC-compatible 128-bit helper routines.
// Visual Studio does not support GCC/Clang's built-in 128-bit integer type,
// so these functions operate directly on the two 64-bit limbs of U128.

static inline bool u128_is_zero(U128 x) {
    return x.lo == 0ULL && x.hi == 0ULL;
}

static inline void add_32x32_product_to_limbs(
    unsigned long long limbs[6],
    uint32_t a,
    uint32_t b,
    int offset)
{
    const unsigned long long MASK32 = 0xFFFFFFFFULL;
    const unsigned long long product =
        static_cast<unsigned long long>(a) * static_cast<unsigned long long>(b);

    unsigned long long low = product & MASK32;
    unsigned long long high = product >> 32;

    unsigned long long sum = limbs[offset] + low;
    limbs[offset] = sum & MASK32;
    unsigned long long carry = sum >> 32;

    sum = limbs[offset + 1] + high + carry;
    limbs[offset + 1] = sum & MASK32;
    carry = sum >> 32;

    int k = offset + 2;
    while (carry != 0ULL && k < 6) {
        sum = limbs[k] + carry;
        limbs[k] = sum & MASK32;
        carry = sum >> 32;
        ++k;
    }
}

static inline U128 u128_mul_u64(U128 a, unsigned long long m) {
    const uint32_t a0 = static_cast<uint32_t>(a.lo & 0xFFFFFFFFULL);
    const uint32_t a1 = static_cast<uint32_t>((a.lo >> 32) & 0xFFFFFFFFULL);
    const uint32_t a2 = static_cast<uint32_t>(a.hi & 0xFFFFFFFFULL);
    const uint32_t a3 = static_cast<uint32_t>((a.hi >> 32) & 0xFFFFFFFFULL);

    const uint32_t m0 = static_cast<uint32_t>(m & 0xFFFFFFFFULL);
    const uint32_t m1 = static_cast<uint32_t>((m >> 32) & 0xFFFFFFFFULL);

    unsigned long long limbs[6] = {0ULL, 0ULL, 0ULL, 0ULL, 0ULL, 0ULL};

    add_32x32_product_to_limbs(limbs, a0, m0, 0);
    add_32x32_product_to_limbs(limbs, a0, m1, 1);
    add_32x32_product_to_limbs(limbs, a1, m0, 1);
    add_32x32_product_to_limbs(limbs, a1, m1, 2);
    add_32x32_product_to_limbs(limbs, a2, m0, 2);
    add_32x32_product_to_limbs(limbs, a2, m1, 3);
    add_32x32_product_to_limbs(limbs, a3, m0, 3);
    add_32x32_product_to_limbs(limbs, a3, m1, 4);

    // Return the low 128 bits. Valid poker counts are expected to fit in U128.
    U128 out;
    out.lo = (limbs[0] & 0xFFFFFFFFULL) | (limbs[1] << 32);
    out.hi = (limbs[2] & 0xFFFFFFFFULL) | (limbs[3] << 32);
    return out;
}


static U128 u128_divmod_u32(U128 x, uint32_t d, uint32_t* remainder_out) {
    if (d == 0U) {
        throw std::runtime_error("u128 division by zero.");
    }

    uint32_t in[4];
    in[0] = static_cast<uint32_t>(x.lo & 0xFFFFFFFFULL);
    in[1] = static_cast<uint32_t>((x.lo >> 32) & 0xFFFFFFFFULL);
    in[2] = static_cast<uint32_t>(x.hi & 0xFFFFFFFFULL);
    in[3] = static_cast<uint32_t>((x.hi >> 32) & 0xFFFFFFFFULL);

    uint32_t q[4] = {0U, 0U, 0U, 0U};
    unsigned long long rem = 0ULL;

    for (int i = 3; i >= 0; --i) {
        const unsigned long long cur = (rem << 32) | static_cast<unsigned long long>(in[i]);
        q[i] = static_cast<uint32_t>(cur / static_cast<unsigned long long>(d));
        rem = cur % static_cast<unsigned long long>(d);
    }

    if (remainder_out) {
        *remainder_out = static_cast<uint32_t>(rem);
    }

    U128 out;
    out.lo = static_cast<unsigned long long>(q[0]) |
             (static_cast<unsigned long long>(q[1]) << 32);
    out.hi = static_cast<unsigned long long>(q[2]) |
             (static_cast<unsigned long long>(q[3]) << 32);
    return out;
}

static U128 u128_div_u32(U128 x, uint32_t d) {
    return u128_divmod_u32(x, d, nullptr);
}

static std::string u128_to_string(U128 x) {
    if (u128_is_zero(x)) return "0";

    std::string s;
    while (!u128_is_zero(x)) {
        uint32_t rem = 0;
        x = u128_divmod_u32(x, 10U, &rem);
        s.push_back(static_cast<char>('0' + rem));
    }

    std::reverse(s.begin(), s.end());
    return s;
}

using ResultArray = std::array<U128, CATEGORY_COUNT>;

static ResultArray zero_result_array() {
    ResultArray a{};
    for (int i = 0; i < CATEGORY_COUNT; ++i) a[i] = u128_zero();
    return a;
}

static unsigned long long choose_host(int n, int k) {
    if (k < 0 || k > n) return 0ULL;
    if (k > n - k) k = n - k;
    unsigned long long r = 1ULL;
    for (int i = 1; i <= k; ++i) {
        r = (r * static_cast<unsigned long long>(n - k + i)) / static_cast<unsigned long long>(i);
    }
    return r;
}


static void unrank_comb5_50_host(unsigned long long rank, int out[5]) {
    int x = 0;
    for (int i = 0; i < 5; ++i) {
        const int rem = 5 - i - 1;
        for (int c = x; c <= 50 - (5 - i); ++c) {
            const unsigned long long cnt = choose_host(50 - c - 1, rem);
            if (rank < cnt) {
                out[i] = c;
                x = c + 1;
                break;
            }
            rank -= cnt;
        }
    }
}

static inline int eval7_tpt_host(const int* hr, const unsigned char cards[7]) {
    int p = hr[53 + cards[0]];
    p = hr[p + cards[1]];
    p = hr[p + cards[2]];
    p = hr[p + cards[3]];
    p = hr[p + cards[4]];
    p = hr[p + cards[5]];
    p = hr[p + cards[6]];
    return p;
}

static void rank_one_board_cpu(
    const int* hr,
    const unsigned char* reduced52,
    unsigned long long board_index,
    unsigned short& hero_rank,
    unsigned short* erow)
{
    int combo[5];
    unrank_comb5_50_host(board_index, combo);

    bool on_board[50];
    for (int i = 0; i < 50; ++i) on_board[i] = false;

    unsigned char board[5];
    for (int i = 0; i < 5; ++i) {
        on_board[combo[i]] = true;
        board[i] = reduced52[combo[i]];
    }

    unsigned char rem[45];
    int rn = 0;
    for (int i = 0; i < 50; ++i) {
        if (!on_board[i]) rem[rn++] = reduced52[i];
    }
    if (rn != 45) {
        throw std::runtime_error("Internal error: CPU board ranker rem count != 45");
    }

    const unsigned char hero0 = reduced52[50];
    const unsigned char hero1 = reduced52[51];

    unsigned char hcards[7];
    hcards[0] = hero0;
    hcards[1] = hero1;
    hcards[2] = board[0];
    hcards[3] = board[1];
    hcards[4] = board[2];
    hcards[5] = board[3];
    hcards[6] = board[4];
    hero_rank = static_cast<unsigned short>(eval7_tpt_host(hr, hcards));

    int e = 0;
    for (int a = 0; a < 45; ++a) {
        for (int b = a + 1; b < 45; ++b) {
            unsigned char cards[7];
            cards[0] = rem[a];
            cards[1] = rem[b];
            cards[2] = board[0];
            cards[3] = board[1];
            cards[4] = board[2];
            cards[5] = board[3];
            cards[6] = board[4];
            erow[e++] = static_cast<unsigned short>(eval7_tpt_host(hr, cards));
        }
    }
}

static void rank_boards_cpu(
    const int* hr,
    const unsigned char* reduced52,
    unsigned long long start_board,
    int board_count_this_chunk,
    unsigned short* hero_ranks,
    unsigned short* edge_ranks)
{
    for (int tid = 0; tid < board_count_this_chunk; ++tid) {
        rank_one_board_cpu(
            hr,
            reduced52,
            start_board + static_cast<unsigned long long>(tid),
            hero_ranks[tid],
            edge_ranks + static_cast<size_t>(tid) * EDGE_COUNT);
    }
}

static void build_rank_matrix(const unsigned short* edge_ranks, unsigned short mat[45][45]) {
    for (int i = 0; i < 45; ++i) {
        for (int j = 0; j < 45; ++j) mat[i][j] = 0;
    }
    int e = 0;
    for (int i = 0; i < 45; ++i) {
        for (int j = i + 1; j < 45; ++j) {
            mat[i][j] = mat[j][i] = edge_ranks[e++];
        }
    }
}

struct TypeGraph {
    int type_count = 0;
    std::vector<unsigned char> sizes;
    std::vector<unsigned short> rank; // type_count * type_count, symmetric
};

static bool verify_partition_uniform(
    const std::vector<std::vector<int>>& classes,
    const unsigned short mat[45][45],
    std::vector<unsigned char>& mark_singleton)
{
    bool ok = true;
    mark_singleton.assign(classes.size(), 0);

    for (size_t a = 0; a < classes.size(); ++a) {
        for (size_t b = a; b < classes.size(); ++b) {
            bool have = false;
            unsigned short first = 0;

            for (int va : classes[a]) {
                for (int vb : classes[b]) {
                    if (va == vb) continue;
                    if (a == b && va > vb) continue;
                    const unsigned short r = mat[va][vb];
                    if (!have) {
                        first = r;
                        have = true;
                    } else if (r != first) {
                        ok = false;
                        mark_singleton[a] = 1;
                        mark_singleton[b] = 1;
                    }
                }
            }
        }
    }

    return ok;
}

static TypeGraph build_exact_type_graph(const unsigned short mat[45][45]) {
    // Conservative initial grouping: identical labelled rank rows.
    // This is exact but may miss suit-permutation symmetry. A verification loop
    // below guarantees all final class-to-class edge ranks are uniform.
    std::vector<std::string> sigs(45);
    for (int v = 0; v < 45; ++v) {
        std::string s;
        s.reserve(45 * 2);
        for (int u = 0; u < 45; ++u) {
            unsigned short r = (u == v) ? 65535u : mat[v][u];
            s.push_back(static_cast<char>(r & 0xFF));
            s.push_back(static_cast<char>((r >> 8) & 0xFF));
        }
        sigs[v] = std::move(s);
    }

    std::vector<int> order(45);
    std::iota(order.begin(), order.end(), 0);
    std::sort(order.begin(), order.end(), [&](int a, int b) {
        return sigs[a] < sigs[b];
    });

    std::vector<std::vector<int>> classes;
    for (int v : order) {
        if (classes.empty() || sigs[classes.back().front()] != sigs[v]) {
            classes.push_back(std::vector<int>{v});
        } else {
            classes.back().push_back(v);
        }
    }

    while (true) {
        std::vector<unsigned char> mark;
        if (verify_partition_uniform(classes, mat, mark)) break;

        std::vector<std::vector<int>> next;
        for (size_t i = 0; i < classes.size(); ++i) {
            if (!mark[i]) {
                next.push_back(classes[i]);
            } else {
                for (int v : classes[i]) {
                    next.push_back(std::vector<int>{v});
                }
            }
        }

        if (next.size() == classes.size()) {
            classes.swap(next);
            break;
        }
        classes.swap(next);
    }

    TypeGraph g;
    g.type_count = static_cast<int>(classes.size());
    g.sizes.resize(g.type_count);
    g.rank.assign(static_cast<size_t>(g.type_count) * g.type_count, 0);

    for (int i = 0; i < g.type_count; ++i) {
        g.sizes[i] = static_cast<unsigned char>(classes[i].size());
    }

    for (int a = 0; a < g.type_count; ++a) {
        for (int b = a; b < g.type_count; ++b) {
            unsigned short r = 0;
            bool have = false;
            for (int va : classes[a]) {
                for (int vb : classes[b]) {
                    if (va == vb) continue;
                    if (a == b && va > vb) continue;
                    r = mat[va][vb];
                    have = true;
                    break;
                }
                if (have) break;
            }
            g.rank[static_cast<size_t>(a) * g.type_count + b] = r;
            g.rank[static_cast<size_t>(b) * g.type_count + a] = r;
        }
    }

    return g;
}


struct HistEntry {
    unsigned short top_rank;
    unsigned char top_count;
    U128 count;
};

struct StateKey {
    unsigned char seats_left;
    unsigned char count_len;
    unsigned char counts[45];

    StateKey() : seats_left(0), count_len(0), counts{} {}
};

struct StateKeyHash {
    size_t operator()(const StateKey& k) const {
        // 64-bit FNV-1a over fixed bytes. Avoids heap allocation from
        // std::string state keys.
        unsigned long long h = 1469598103934665603ULL;
        auto mix = [&](unsigned char x) {
            h ^= static_cast<unsigned long long>(x);
            h *= 1099511628211ULL;
        };

        mix(k.seats_left);
        mix(k.count_len);
        for (int i = 0; i < static_cast<int>(k.count_len); ++i) {
            mix(k.counts[i]);
        }

        return static_cast<size_t>(h);
    }
};

struct StateKeyEq {
    bool operator()(const StateKey& a, const StateKey& b) const {
        if (a.seats_left != b.seats_left || a.count_len != b.count_len) return false;
        for (int i = 0; i < static_cast<int>(a.count_len); ++i) {
            if (a.counts[i] != b.counts[i]) return false;
        }
        return true;
    }
};

struct HistDP {
    int target_opp = 8;
    unsigned short hero_rank = 0;
    const TypeGraph* g = nullptr;

    // Keyed only by remaining exact card-type counts and seats left.
    // This is the high-player specialization: no prefix counts for 2..8 players
    // are generated when the requested player count is 9.
    std::unordered_map<StateKey, std::vector<HistEntry>, StateKeyHash, StateKeyEq> memo;
    uint64_t states_visited = 0;

    StateKey make_key(const std::vector<unsigned char>& counts, int seats_left) const {
        StateKey k;
        k.seats_left = static_cast<unsigned char>(seats_left);
        k.count_len = static_cast<unsigned char>(counts.size());
        for (size_t i = 0; i < counts.size() && i < 45; ++i) {
            k.counts[i] = counts[i];
        }
        return k;
    }

    static void add_to_hist_map(
        std::unordered_map<unsigned int, U128>& acc,
        unsigned short rank,
        unsigned char top_count,
        const U128& value)
    {
        const unsigned int key =
            (static_cast<unsigned int>(rank) << 8) |
            static_cast<unsigned int>(top_count);
        auto it = acc.find(key);
        if (it == acc.end()) {
            acc.emplace(key, value);
        } else {
            u128_add_inplace(it->second, value);
        }
    }

    std::vector<HistEntry> dfs(std::vector<unsigned char>& counts, int seats_left) {
        if (seats_left == 0) {
            return std::vector<HistEntry>{HistEntry{0, 0, u128_from_u64(1ULL)}};
        }

        int live_cards = 0;
        for (unsigned char c : counts) live_cards += static_cast<int>(c);
        if (live_cards < 2 * seats_left) {
            return std::vector<HistEntry>();
        }

        const StateKey key = make_key(counts, seats_left);
        auto mit = memo.find(key);
        if (mit != memo.end()) {
            return mit->second;
        }

        ++states_visited;

        std::unordered_map<unsigned int, U128> acc;
        acc.reserve(256);
        acc.max_load_factor(0.7f);

        const int C = g->type_count;

        for (int a = 0; a < C; ++a) {
            const int ca = counts[a];
            if (ca <= 0) continue;

            for (int b = a; b < C; ++b) {
                const int cb = counts[b];
                if (cb <= 0) continue;

                unsigned long long ways = 0ULL;
                if (a == b) {
                    if (ca < 2) continue;
                    ways = static_cast<unsigned long long>(ca) *
                           static_cast<unsigned long long>(ca - 1) / 2ULL;
                } else {
                    ways = static_cast<unsigned long long>(ca) *
                           static_cast<unsigned long long>(cb);
                }
                if (ways == 0ULL) continue;

                const unsigned short r = g->rank[static_cast<size_t>(a) * C + b];
                if (r == 0) continue;

                counts[a] = static_cast<unsigned char>(counts[a] - 1);
                counts[b] = static_cast<unsigned char>(counts[b] - 1);

                const std::vector<HistEntry> sub = dfs(counts, seats_left - 1);

                counts[b] = static_cast<unsigned char>(counts[b] + 1);
                counts[a] = static_cast<unsigned char>(counts[a] + 1);

                for (const HistEntry& e : sub) {
                    unsigned short nr = e.top_rank;
                    unsigned char nc = e.top_count;

                    if (r > nr) {
                        nr = r;
                        nc = 1;
                    } else if (r == nr) {
                        nc = static_cast<unsigned char>(nc + 1);
                    }

                    add_to_hist_map(acc, nr, nc, u128_mul_u64(e.count, ways));
                }
            }
        }

        std::vector<HistEntry> out;
        out.reserve(acc.size());
        for (const auto& kv : acc) {
            const unsigned int key2 = kv.first;
            HistEntry e;
            e.top_rank = static_cast<unsigned short>(key2 >> 8);
            e.top_count = static_cast<unsigned char>(key2 & 0xFFu);
            e.count = kv.second;
            out.push_back(e);
        }

        memo.emplace(key, out);
        return out;
    }

    int category_for(int total_players, unsigned short top_rank, unsigned char top_count) const {
        const int base = HOST_CAT_BASE[total_players];

        if (top_rank < hero_rank) {
            return base + 0; // hero strict win
        }

        if (top_rank == hero_rank) {
            const int tie_size = static_cast<int>(top_count) + 1; // hero plus tied opponents
            return base + 1 + (tie_size - 2);
        }

        if (top_count == 1) {
            return base + total_players; // opponent strict win
        }

        const int tie_size = static_cast<int>(top_count);
        return base + total_players + 1 + (tie_size - 2);
    }

    ResultArray run_exact_total_players(const TypeGraph& graph, unsigned short h_rank, int total_players) {
        g = &graph;
        hero_rank = h_rank;
        target_opp = total_players - 1;
        memo.clear();
        memo.reserve(200000);
        memo.max_load_factor(0.7f);
        states_visited = 0;

        ResultArray out = zero_result_array();
        std::vector<unsigned char> counts = g->sizes;
        std::vector<HistEntry> hist = dfs(counts, target_opp);

        for (const HistEntry& e : hist) {
            const int cat = category_for(total_players, e.top_rank, e.top_count);
            u128_add_inplace(out[cat], e.count);
        }

        return out;
    }
};

struct BoardCacheEntry {
    ResultArray result;
    int type_count;
    uint64_t states_visited;
};

struct ChunkThreadStats {
    ResultArray totals;
    unsigned long long boards_done;
    unsigned long long total_type_count;
    int max_type_count;
    unsigned long long dp_states;
    unsigned long long cache_hits;

    ChunkThreadStats()
        : totals(zero_result_array()),
          boards_done(0ULL),
          total_type_count(0ULL),
          max_type_count(0),
          dp_states(0ULL),
          cache_hits(0ULL)
    {}
};


// -----------------------------------------------------------------------------
// Specialized exact 5-player meet-in-the-middle board counter.
//
// For each board:
//   * The GPU has already ranked the 990 possible opponent hands.
//   * This counter builds all C(45,4) four-card sets.
//   * Each four-card set represents the two cards used by seats P2/P3
//     or by seats P4/P5.
//   * A four-card set has 6 ordered two-seat pairings, represented as
//     three unordered pair partitions each with multiplicity 2.
//   * It counts compatible second two-seat blocks by inclusion-exclusion
//     over the four cards in the first block.
//   * No recursive DP table is used.
// -----------------------------------------------------------------------------

struct MitFourSet {
    unsigned char c[4];
    int e01;
    int e02;
    int e03;
    int e12;
    int e13;
    int e23;
    int t012;
    int t013;
    int t023;
    int t123;
};

struct MitBucket {
    int rank_idx;
    unsigned char top_count;
    unsigned int ways;
};

struct MitPrecomp {
    int edge_id[45][45];
    int triple_id[45][45][45];
    std::vector<MitFourSet> sets;

    MitPrecomp() {
        for (int i = 0; i < 45; ++i) {
            for (int j = 0; j < 45; ++j) {
                edge_id[i][j] = -1;
            }
        }

        int eid = 0;
        for (int a = 0; a < 45; ++a) {
            for (int b = a + 1; b < 45; ++b) {
                edge_id[a][b] = edge_id[b][a] = eid++;
            }
        }

        for (int a = 0; a < 45; ++a) {
            for (int b = 0; b < 45; ++b) {
                for (int c = 0; c < 45; ++c) {
                    triple_id[a][b][c] = -1;
                }
            }
        }

        int tid = 0;
        for (int a = 0; a < 45; ++a) {
            for (int b = a + 1; b < 45; ++b) {
                for (int c = b + 1; c < 45; ++c) {
                    triple_id[a][b][c] = triple_id[a][c][b] =
                    triple_id[b][a][c] = triple_id[b][c][a] =
                    triple_id[c][a][b] = triple_id[c][b][a] = tid++;
                }
            }
        }

        sets.reserve(148995);
        for (int a = 0; a < 45; ++a) {
            for (int b = a + 1; b < 45; ++b) {
                for (int c = b + 1; c < 45; ++c) {
                    for (int d = c + 1; d < 45; ++d) {
                        MitFourSet fs;
                        fs.c[0] = static_cast<unsigned char>(a);
                        fs.c[1] = static_cast<unsigned char>(b);
                        fs.c[2] = static_cast<unsigned char>(c);
                        fs.c[3] = static_cast<unsigned char>(d);
                        fs.e01 = edge_id[a][b];
                        fs.e02 = edge_id[a][c];
                        fs.e03 = edge_id[a][d];
                        fs.e12 = edge_id[b][c];
                        fs.e13 = edge_id[b][d];
                        fs.e23 = edge_id[c][d];
                        fs.t012 = triple_id[a][b][c];
                        fs.t013 = triple_id[a][b][d];
                        fs.t023 = triple_id[a][c][d];
                        fs.t123 = triple_id[b][c][d];
                        sets.push_back(fs);
                    }
                }
            }
        }
    }
};

static const MitPrecomp& mit_precomp() {
    static MitPrecomp pc;
    return pc;
}

struct MitBoardCounter {
    std::vector<unsigned short> ranks;
    std::vector<int> rank_index;
    std::vector<unsigned int> agg1;
    std::vector<unsigned int> agg2;
    int K = 0;
    int agg_count = 0;
    int hero_pos = 0;
    bool hero_eq = false;
    unsigned long long last_unique_ranks = 0ULL;

    MitBoardCounter() : rank_index(65536, -1) {}

    static int cat_offset(unsigned short hero_rank, unsigned short top_rank, int top_count) {
        if (top_rank < hero_rank) {
            return 0; // hero strict win
        }
        if (top_rank == hero_rank) {
            // hero plus top_count tied opponents, so top_count 1..4 maps to offsets 1..4.
            return top_count;
        }
        if (top_count == 1) {
            return 5; // opponent strict winner
        }
        return 6 + (top_count - 2); // opponent-only tie size 2..4
    }

    static void add_bucket(MitBucket* buckets, int& n, int rank_idx, unsigned char top_count, unsigned int ways) {
        for (int i = 0; i < n; ++i) {
            if (buckets[i].rank_idx == rank_idx && buckets[i].top_count == top_count) {
                buckets[i].ways += ways;
                return;
            }
        }
        buckets[n].rank_idx = rank_idx;
        buckets[n].top_count = top_count;
        buckets[n].ways = ways;
        ++n;
    }

    void make_block_hist(const MitFourSet& fs, const unsigned short* erow, MitBucket* buckets, int& n) const {
        n = 0;

        const unsigned short r01 = erow[fs.e01];
        const unsigned short r02 = erow[fs.e02];
        const unsigned short r03 = erow[fs.e03];
        const unsigned short r12 = erow[fs.e12];
        const unsigned short r13 = erow[fs.e13];
        const unsigned short r23 = erow[fs.e23];

        // Partition (01,23), with two seat orders.
        {
            const unsigned short top = std::max(r01, r23);
            const unsigned char cnt = static_cast<unsigned char>((r01 == r23) ? 2 : 1);
            add_bucket(buckets, n, rank_index[top], cnt, 2U);
        }

        // Partition (02,13), with two seat orders.
        {
            const unsigned short top = std::max(r02, r13);
            const unsigned char cnt = static_cast<unsigned char>((r02 == r13) ? 2 : 1);
            add_bucket(buckets, n, rank_index[top], cnt, 2U);
        }

        // Partition (03,12), with two seat orders.
        {
            const unsigned short top = std::max(r03, r12);
            const unsigned char cnt = static_cast<unsigned char>((r03 == r12) ? 2 : 1);
            add_bucket(buckets, n, rank_index[top], cnt, 2U);
        }
    }

    inline int agg_total_id() const { return 0; }
    inline int agg_card_id(int c) const { return 1 + c; }
    inline int agg_pair_id(int edge_id) const { return 1 + 45 + edge_id; }
    inline int agg_triple_id(int triple_id) const { return 1 + 45 + EDGE_COUNT + triple_id; }

    void add_to_agg(int agg_id, int rank_idx, unsigned char top_count, unsigned int ways) {
        const size_t off = static_cast<size_t>(agg_id) * static_cast<size_t>(K) + static_cast<size_t>(rank_idx);
        if (top_count == 1) {
            agg1[off] += ways;
        } else {
            agg2[off] += ways;
        }
    }

    void add_hist_to_aggregates(const MitFourSet& fs, const MitBucket* buckets, int n) {
        const int card_ids[4] = {
            agg_card_id(fs.c[0]), agg_card_id(fs.c[1]), agg_card_id(fs.c[2]), agg_card_id(fs.c[3])
        };
        const int pair_ids[6] = {
            agg_pair_id(fs.e01), agg_pair_id(fs.e02), agg_pair_id(fs.e03),
            agg_pair_id(fs.e12), agg_pair_id(fs.e13), agg_pair_id(fs.e23)
        };
        const int triple_ids[4] = {
            agg_triple_id(fs.t012), agg_triple_id(fs.t013),
            agg_triple_id(fs.t023), agg_triple_id(fs.t123)
        };

        for (int i = 0; i < n; ++i) {
            const MitBucket& b = buckets[i];
            add_to_agg(agg_total_id(), b.rank_idx, b.top_count, b.ways);
            for (int x = 0; x < 4; ++x) add_to_agg(card_ids[x], b.rank_idx, b.top_count, b.ways);
            for (int x = 0; x < 6; ++x) add_to_agg(pair_ids[x], b.rank_idx, b.top_count, b.ways);
            for (int x = 0; x < 4; ++x) add_to_agg(triple_ids[x], b.rank_idx, b.top_count, b.ways);
        }
    }

    unsigned long long range_sum(const std::vector<unsigned int>& agg, int agg_id, int lo, int hi) const {
        if (K <= 0) return 0ULL;
        if (hi < lo) return 0ULL;
        if (lo < 0) lo = 0;
        if (hi >= K) hi = K - 1;
        if (hi < lo) return 0ULL;

        const size_t base = static_cast<size_t>(agg_id) * static_cast<size_t>(K);
        unsigned long long out = agg[base + static_cast<size_t>(hi)];
        if (lo > 0) {
            out -= agg[base + static_cast<size_t>(lo - 1)];
        }
        return out;
    }

    unsigned long long point_sum(const std::vector<unsigned int>& agg, int agg_id, int idx) const {
        return range_sum(agg, agg_id, idx, idx);
    }

    void apply_agg(long long cats[9], int sign, int agg_id, int a_rank_idx, unsigned char a_top_count) const {
        const unsigned short a_rank = ranks[static_cast<size_t>(a_rank_idx)];
        const int cat_a = cat_offset(ranks[static_cast<size_t>(hero_pos >= K ? K - 1 : hero_pos)], a_rank, a_top_count);
        // The line above is not used for hero rank. Kept separate below to avoid ambiguity.
        (void)cat_a;
    }

    void apply_agg_with_hero(long long cats[9], int sign, int agg_id, int a_rank_idx,
                             unsigned char a_top_count, unsigned short hero_rank) const
    {
        const unsigned short a_rank = ranks[static_cast<size_t>(a_rank_idx)];

        // B top rank less than A top rank.
        {
            const unsigned long long n =
                range_sum(agg1, agg_id, 0, a_rank_idx - 1) +
                range_sum(agg2, agg_id, 0, a_rank_idx - 1);
            if (n) {
                const int cat = cat_offset(hero_rank, a_rank, a_top_count);
                cats[cat] += static_cast<long long>(sign) * static_cast<long long>(n);
            }
        }

        // B top rank equal to A top rank.
        {
            const unsigned long long n1 = point_sum(agg1, agg_id, a_rank_idx);
            const unsigned long long n2 = point_sum(agg2, agg_id, a_rank_idx);
            if (n1) {
                const int cat = cat_offset(hero_rank, a_rank, static_cast<int>(a_top_count) + 1);
                cats[cat] += static_cast<long long>(sign) * static_cast<long long>(n1);
            }
            if (n2) {
                const int cat = cat_offset(hero_rank, a_rank, static_cast<int>(a_top_count) + 2);
                cats[cat] += static_cast<long long>(sign) * static_cast<long long>(n2);
            }
        }

        // B top rank greater than A top rank.
        if (a_rank < hero_rank) {
            // B top rank between A and hero: hero still wins strictly.
            const int below_hero_hi = hero_pos - 1;
            const int between_lo = a_rank_idx + 1;
            if (below_hero_hi >= between_lo) {
                const unsigned long long n =
                    range_sum(agg1, agg_id, between_lo, below_hero_hi) +
                    range_sum(agg2, agg_id, between_lo, below_hero_hi);
                cats[0] += static_cast<long long>(sign) * static_cast<long long>(n);
            }

            // B top rank exactly equal to hero.
            if (hero_eq && hero_pos > a_rank_idx) {
                const unsigned long long n1 = point_sum(agg1, agg_id, hero_pos);
                const unsigned long long n2 = point_sum(agg2, agg_id, hero_pos);
                cats[1] += static_cast<long long>(sign) * static_cast<long long>(n1);
                cats[2] += static_cast<long long>(sign) * static_cast<long long>(n2);
            }

            // B top rank greater than hero.
            const int start = hero_pos + (hero_eq ? 1 : 0);
            if (start < K) {
                const unsigned long long n1 = range_sum(agg1, agg_id, start, K - 1);
                const unsigned long long n2 = range_sum(agg2, agg_id, start, K - 1);
                cats[5] += static_cast<long long>(sign) * static_cast<long long>(n1);
                cats[6] += static_cast<long long>(sign) * static_cast<long long>(n2);
            }
        } else {
            // A is already at or above hero. Any B greater than A is an opponent result.
            const int start = a_rank_idx + 1;
            if (start < K) {
                const unsigned long long n1 = range_sum(agg1, agg_id, start, K - 1);
                const unsigned long long n2 = range_sum(agg2, agg_id, start, K - 1);
                cats[5] += static_cast<long long>(sign) * static_cast<long long>(n1);
                cats[6] += static_cast<long long>(sign) * static_cast<long long>(n2);
            }
        }
    }

    void apply_own_hist(long long cats[9], int sign, const MitBucket* b_hist, int b_n,
                        int a_rank_idx, unsigned char a_top_count, unsigned short hero_rank) const
    {
        const unsigned short a_rank = ranks[static_cast<size_t>(a_rank_idx)];
        for (int i = 0; i < b_n; ++i) {
            const MitBucket& b = b_hist[i];
            const unsigned short b_rank = ranks[static_cast<size_t>(b.rank_idx)];
            unsigned short top = a_rank;
            int top_count = a_top_count;

            if (b_rank > top) {
                top = b_rank;
                top_count = b.top_count;
            } else if (b_rank == top) {
                top_count += b.top_count;
            }

            const int cat = cat_offset(hero_rank, top, top_count);
            cats[cat] += static_cast<long long>(sign) *
                         static_cast<long long>(b.ways);
        }
    }

    ResultArray compute(unsigned short hero_rank, const unsigned short* erow) {
        const MitPrecomp& pc = mit_precomp();

        ranks.assign(erow, erow + EDGE_COUNT);
        std::sort(ranks.begin(), ranks.end());
        ranks.erase(std::unique(ranks.begin(), ranks.end()), ranks.end());
        K = static_cast<int>(ranks.size());
        last_unique_ranks = static_cast<unsigned long long>(K);

        std::fill(rank_index.begin(), rank_index.end(), -1);
        for (int i = 0; i < K; ++i) {
            rank_index[ranks[static_cast<size_t>(i)]] = i;
        }

        std::vector<unsigned short>::const_iterator hp =
            std::lower_bound(ranks.begin(), ranks.end(), hero_rank);
        hero_pos = static_cast<int>(hp - ranks.begin());
        hero_eq = (hp != ranks.end() && *hp == hero_rank);

        agg_count = 1 + 45 + EDGE_COUNT + 14190;
        const size_t cells = static_cast<size_t>(agg_count) * static_cast<size_t>(K);
        agg1.assign(cells, 0U);
        agg2.assign(cells, 0U);

        MitBucket hist[3];
        int h_n = 0;

        for (const MitFourSet& fs : pc.sets) {
            make_block_hist(fs, erow, hist, h_n);
            add_hist_to_aggregates(fs, hist, h_n);
        }

        // Convert aggregate rank counts into prefix sums by rank.
        for (int aid = 0; aid < agg_count; ++aid) {
            const size_t base = static_cast<size_t>(aid) * static_cast<size_t>(K);
            for (int i = 1; i < K; ++i) {
                agg1[base + static_cast<size_t>(i)] += agg1[base + static_cast<size_t>(i - 1)];
                agg2[base + static_cast<size_t>(i)] += agg2[base + static_cast<size_t>(i - 1)];
            }
        }

        ResultArray out = zero_result_array();
        const int base_cat = HOST_CAT_BASE[5];

        for (const MitFourSet& fs : pc.sets) {
            make_block_hist(fs, erow, hist, h_n);

            const int card_ids[4] = {
                agg_card_id(fs.c[0]), agg_card_id(fs.c[1]), agg_card_id(fs.c[2]), agg_card_id(fs.c[3])
            };
            const int pair_ids[6] = {
                agg_pair_id(fs.e01), agg_pair_id(fs.e02), agg_pair_id(fs.e03),
                agg_pair_id(fs.e12), agg_pair_id(fs.e13), agg_pair_id(fs.e23)
            };
            const int triple_ids[4] = {
                agg_triple_id(fs.t012), agg_triple_id(fs.t013),
                agg_triple_id(fs.t023), agg_triple_id(fs.t123)
            };

            for (int ai = 0; ai < h_n; ++ai) {
                const MitBucket& a = hist[ai];
                long long cats[9] = {0,0,0,0,0,0,0,0,0};

                apply_agg_with_hero(cats, +1, agg_total_id(), a.rank_idx, a.top_count, hero_rank);

                for (int x = 0; x < 4; ++x) {
                    apply_agg_with_hero(cats, -1, card_ids[x], a.rank_idx, a.top_count, hero_rank);
                }
                for (int x = 0; x < 6; ++x) {
                    apply_agg_with_hero(cats, +1, pair_ids[x], a.rank_idx, a.top_count, hero_rank);
                }
                for (int x = 0; x < 4; ++x) {
                    apply_agg_with_hero(cats, -1, triple_ids[x], a.rank_idx, a.top_count, hero_rank);
                }

                // Inclusion-exclusion term for B blocks containing all four cards of A's set.
                apply_own_hist(cats, +1, hist, h_n, a.rank_idx, a.top_count, hero_rank);

                for (int c = 0; c < 9; ++c) {
                    if (cats[c] < 0) {
                        std::ostringstream oss;
                        oss << "MIT internal negative category count: category " << c
                            << " value " << cats[c];
                        throw std::runtime_error(oss.str());
                    }
                    if (cats[c] > 0) {
                        const unsigned long long add =
                            static_cast<unsigned long long>(cats[c]) *
                            static_cast<unsigned long long>(a.ways);
                        u128_add_inplace(out[base_cat + c], u128_from_u64(add));
                    }
                }
            }
        }

        // Per-board conservation check.
        U128 board_total = u128_zero();
        for (int c = 0; c < 9; ++c) {
            u128_add_inplace(board_total, out[base_cat + c]);
        }
        const unsigned long long expected_board_total = 543194051400ULL;
        if (board_total.hi != 0ULL || board_total.lo != expected_board_total) {
            std::ostringstream oss;
            oss << "MIT board total mismatch: got " << u128_to_string(board_total)
                << ", expected " << expected_board_total;
            throw std::runtime_error(oss.str());
        }

        return out;
    }
};

static std::string make_graph_signature(const TypeGraph& tg, unsigned short hero_rank, int total_players) {
    std::string s;
    const int C = tg.type_count;
    s.reserve(8 + static_cast<size_t>(C) + static_cast<size_t>(C) * C * 2);

    s.push_back(static_cast<char>(total_players));
    s.push_back(static_cast<char>(hero_rank & 0xFF));
    s.push_back(static_cast<char>((hero_rank >> 8) & 0xFF));
    s.push_back(static_cast<char>(C));

    for (int i = 0; i < C; ++i) {
        s.push_back(static_cast<char>(tg.sizes[i]));
    }

    for (int i = 0; i < C * C; ++i) {
        const unsigned short r = tg.rank[i];
        s.push_back(static_cast<char>(r & 0xFF));
        s.push_back(static_cast<char>((r >> 8) & 0xFF));
    }

    return s;
}

static int parse_tpt_card(const std::string& s) {
    if (s.size() < 2) return -1;
    char rch = static_cast<char>(std::toupper(static_cast<unsigned char>(s[0])));
    char sch = static_cast<char>(std::tolower(static_cast<unsigned char>(s[1])));

    int rank = -1;
    if (rch >= '2' && rch <= '9') rank = rch - '0';
    else if (rch == 'T') rank = 10;
    else if (rch == 'J') rank = 11;
    else if (rch == 'Q') rank = 12;
    else if (rch == 'K') rank = 13;
    else if (rch == 'A') rank = 14;

    int suit = -1;
    if (sch == 'c') suit = 0;
    else if (sch == 'd') suit = 1;
    else if (sch == 'h') suit = 2;
    else if (sch == 's') suit = 3;

    if (rank < 2 || suit < 0) return -1;

    return (rank - 2) * 4 + suit + 1;
}

static std::vector<int> load_handranks(const std::string& path) {
    std::ifstream in(path.c_str(), std::ios::binary | std::ios::ate);
    if (!in) {
        throw std::runtime_error("Can't open HandRanks.dat");
    }

    const std::streamoff bytes = in.tellg();
    if (bytes <= 0 || (bytes % static_cast<std::streamoff>(sizeof(int))) != 0) {
        throw std::runtime_error("HandRanks.dat has an invalid size.");
    }

    std::vector<int> hr(static_cast<size_t>(bytes / sizeof(int)));
    in.seekg(0, std::ios::beg);
    in.read(reinterpret_cast<char*>(hr.data()), bytes);
    if (!in) {
        throw std::runtime_error("Failed to read HandRanks.dat");
    }
    return hr;
}

static std::string fmt_elapsed(double seconds) {
    unsigned long long s = static_cast<unsigned long long>(seconds + 0.5);
    const unsigned long long d = s / 86400ULL;
    s %= 86400ULL;
    const unsigned long long h = s / 3600ULL;
    s %= 3600ULL;
    const unsigned long long m = s / 60ULL;
    s %= 60ULL;

    std::ostringstream out;
    if (d) out << d << "d ";
    out << h << "h " << m << "m " << s << "s";
    return out.str();
}


static void print_usage(const char* exe) {
    std::cerr
        << "Usage:\n"
        << "  " << exe << " <p1> <p2> <checkpoint_file> <output_csv> [chunk_boards]\n\n"
        << "Examples:\n"
        << "  " << exe << " 0 168 run5p.chk results_5p.csv\n"
        << "  " << exe << " 0 40 part1.chk results_9p_part1.csv 768\n\n"
        << "This program is fixed at exactly 5 total players: hero + 4 opponents.\n"
        << "p1 and p2 are mandatory inclusive hand indexes from 0 to 168, with p1 <= p2.\n"
        << "checkpoint_file is mandatory and is the only resume source.\n"
        << "output_csv is mandatory and is stored in the checkpoint identity.\n"
        << "If the checkpoint exists, p1, p2, and output_csv must match the checkpoint.\n"
        << "Checkpoint interval seconds: " << CHECKPOINT_INTERVAL_SECONDS << "\n"
        << "Pairs are written as AA, KK, etc.; non-pairs as AKs, AKu, etc.\n"
        << "HandRanks.dat must be in the current directory.\n";
}

static char rank_char_from_value_9p(int rank) {
    if (rank >= 2 && rank <= 9) return static_cast<char>('0' + rank);
    if (rank == 10) return 'T';
    if (rank == 11) return 'J';
    if (rank == 12) return 'Q';
    if (rank == 13) return 'K';
    if (rank == 14) return 'A';
    return '?';
}

static std::string card_string_from_rank_suit_9p(int rank, char suit) {
    std::string s;
    s.push_back(rank_char_from_value_9p(rank));
    s.push_back(suit);
    return s;
}

struct StartingHandType9 {
    std::string label;
    std::string card1;
    std::string card2;
};

static std::vector<StartingHandType9> build_169_starting_hand_types_9p() {
    std::vector<StartingHandType9> hands;
    hands.reserve(169);

    // Order: AA, AKs, AKu, AQs, AQu, ..., 22.
    for (int r1 = 14; r1 >= 2; --r1) {
        const char c1 = rank_char_from_value_9p(r1);

        StartingHandType9 pair;
        pair.label = std::string() + c1 + c1;
        pair.card1 = card_string_from_rank_suit_9p(r1, 'c');
        pair.card2 = card_string_from_rank_suit_9p(r1, 'd');
        hands.push_back(pair);

        for (int r2 = r1 - 1; r2 >= 2; --r2) {
            const char c2 = rank_char_from_value_9p(r2);

            StartingHandType9 suited;
            suited.label = std::string() + c1 + c2 + 's';
            suited.card1 = card_string_from_rank_suit_9p(r1, 'c');
            suited.card2 = card_string_from_rank_suit_9p(r2, 'c');
            hands.push_back(suited);

            StartingHandType9 unsuited;
            unsuited.label = std::string() + c1 + c2 + 'u';
            unsuited.card1 = card_string_from_rank_suit_9p(r1, 'c');
            unsuited.card2 = card_string_from_rank_suit_9p(r2, 'd');
            hands.push_back(unsuited);
        }
    }

    if (hands.size() != 169U) {
        throw std::runtime_error("Internal error: expected 169 starting hand types.");
    }
    return hands;
}

static U128 expected_deals_per_hand_5p(unsigned long long all_boards) {
    U128 out = u128_from_u64(all_boards);
    int cards_left = 45;
    for (int opp = 0; opp < 4; ++opp) {
        const unsigned long long c =
            static_cast<unsigned long long>(cards_left) *
            static_cast<unsigned long long>(cards_left - 1) / 2ULL;
        out = u128_mul_u64(out, c);
        cards_left -= 2;
    }
    return out;
}

static void write_csv_row_5p(std::ostream& out, const std::string& label, const ResultArray& totals) {
    const int p = 5;
    const int base = HOST_CAT_BASE[p];

    out << label << ',';

    // Hero strict win.
    out << u128_to_string(totals[base + 0]);

    // Hero ties: 2-way through 5-way.
    for (int tie_size = 2; tie_size <= p; ++tie_size) {
        const int idx = base + 1 + (tie_size - 2);
        out << ',' << u128_to_string(totals[idx]);
    }

    // Player 2 through Player 5 strict wins.
    const U128 per_seat_strict =
        u128_div_u32(totals[base + p], static_cast<uint32_t>(p - 1));
    for (int seat = 2; seat <= 5; ++seat) {
        out << ',' << u128_to_string(per_seat_strict);
    }

    // Opponent-only ties: 2 opponents through 4 opponents.
    for (int tie_size = 2; tie_size <= p - 1; ++tie_size) {
        const int idx = base + p + 1 + (tie_size - 2);
        out << ',' << u128_to_string(totals[idx]);
    }

    out << '\n';
}

static bool file_exists_9p(const std::string& path) {
    std::ifstream in(path.c_str(), std::ios::binary);
    return static_cast<bool>(in);
}

struct Checkpoint9p {
    int p1;
    int p2;
    std::string output_csv;
    unsigned long long all_boards;
    int current_hand;
    unsigned long long next_board;
    double elapsed_seconds;
    unsigned long long total_type_count;
    int max_type_count_seen;
    unsigned long long total_dp_states;
    unsigned long long cache_hits;
    ResultArray current_totals;

    Checkpoint9p()
        : p1(0), p2(0), output_csv(), all_boards(0ULL), current_hand(0), next_board(0ULL),
          elapsed_seconds(0.0), total_type_count(0ULL), max_type_count_seen(0),
          total_dp_states(0ULL), cache_hits(0ULL), current_totals(zero_result_array()) {}
};

static void save_checkpoint_9p(
    const std::string& path,
    int p1,
    int p2,
    const std::string& output_csv,
    unsigned long long all_boards,
    int current_hand,
    unsigned long long next_board,
    double elapsed_seconds,
    unsigned long long total_type_count,
    int max_type_count_seen,
    unsigned long long total_dp_states,
    unsigned long long cache_hits,
    const ResultArray& current_totals)
{
    if (path.empty()) {
        throw std::runtime_error("checkpoint_file must not be empty.");
    }

    const std::string tmp = path + ".tmp";
    std::ofstream out(tmp.c_str(), std::ios::out | std::ios::trunc);
    if (!out) {
        throw std::runtime_error("Failed to open checkpoint temp file for writing: " + tmp);
    }

    out << "HOLDEM5P_169HAND_CHECKPOINT_V1\n";
    out << "gpu_variant " << PROGRAM_VARIANT_NAME << "\n";
    out << "p1 " << p1 << "\n";
    out << "p2 " << p2 << "\n";
    out << "output_csv " << output_csv << "\n";
    out << "all_boards " << all_boards << "\n";
    out << "current_hand " << current_hand << "\n";
    out << "next_board " << next_board << "\n";
    out << "elapsed_seconds " << std::setprecision(17) << elapsed_seconds << "\n";
    out << "total_type_count " << total_type_count << "\n";
    out << "max_type_count_seen " << max_type_count_seen << "\n";
    out << "total_dp_states " << total_dp_states << "\n";
    out << "cache_hits " << cache_hits << "\n";
    for (int i = 0; i < CATEGORY_COUNT; ++i) {
        out << "cat " << i << ' ' << current_totals[i].lo << ' ' << current_totals[i].hi << "\n";
    }
    out << "END\n";
    out.close();

    if (!out) {
        throw std::runtime_error("Failed while writing checkpoint temp file: " + tmp);
    }

    std::remove(path.c_str());
    if (std::rename(tmp.c_str(), path.c_str()) != 0) {
        throw std::runtime_error("Failed to replace checkpoint file: " + path);
    }
}

static bool load_checkpoint_9p(
    const std::string& path,
    int expected_p1,
    int expected_p2,
    const std::string& expected_output_csv,
    unsigned long long expected_all_boards,
    Checkpoint9p& ckpt)
{
    if (!file_exists_9p(path)) {
        return false;
    }

    std::ifstream in(path.c_str());
    if (!in) {
        throw std::runtime_error("Failed to open checkpoint file: " + path);
    }

    std::string marker;
    in >> marker;
    if (marker != "HOLDEM5P_169HAND_CHECKPOINT_V1") {
        throw std::runtime_error("Checkpoint is not a compatible HOLDEM5P 169-hand checkpoint: " + path + ". To restart fresh, delete the checkpoint file or specify a different checkpoint file.");
    }

    ckpt = Checkpoint9p();
    std::string label;

    while (in >> label) {
        if (label == "END") break;

        if (label == "gpu_variant") {
            std::string ignored;
            in >> ignored;
        } else if (label == "p1") {
            in >> ckpt.p1;
        } else if (label == "p2") {
            in >> ckpt.p2;
        } else if (label == "output_csv") {
            in >> std::ws;
            std::getline(in, ckpt.output_csv);
        } else if (label == "all_boards") {
            in >> ckpt.all_boards;
        } else if (label == "current_hand") {
            in >> ckpt.current_hand;
        } else if (label == "next_board") {
            in >> ckpt.next_board;
        } else if (label == "elapsed_seconds") {
            in >> ckpt.elapsed_seconds;
        } else if (label == "total_type_count") {
            in >> ckpt.total_type_count;
        } else if (label == "max_type_count_seen") {
            in >> ckpt.max_type_count_seen;
        } else if (label == "total_dp_states") {
            in >> ckpt.total_dp_states;
        } else if (label == "cache_hits") {
            in >> ckpt.cache_hits;
        } else if (label == "cat") {
            int idx = -1;
            unsigned long long lo = 0ULL;
            unsigned long long hi = 0ULL;
            in >> idx >> lo >> hi;
            if (idx < 0 || idx >= CATEGORY_COUNT) {
                throw std::runtime_error("Checkpoint has invalid category index.");
            }
            ckpt.current_totals[idx].lo = lo;
            ckpt.current_totals[idx].hi = hi;
        } else {
            throw std::runtime_error("Checkpoint has unknown label: " + label);
        }

        if (!in) {
            throw std::runtime_error("Checkpoint is truncated or malformed: " + path);
        }
    }

    if (ckpt.p1 != expected_p1 || ckpt.p2 != expected_p2 || ckpt.output_csv != expected_output_csv) {
        std::ostringstream oss;
        oss << "Checkpoint file exists but its run parameters do not match the command line.\n"
            << "Checkpoint has: p1=" << ckpt.p1
            << ", p2=" << ckpt.p2
            << ", output_csv='" << ckpt.output_csv << "'\n"
            << "Command line has: p1=" << expected_p1
            << ", p2=" << expected_p2
            << ", output_csv='" << expected_output_csv << "'\n"
            << "To restart fresh, delete the checkpoint file or specify a different checkpoint file.";
        throw std::runtime_error(oss.str());
    }
    if (ckpt.all_boards != expected_all_boards) {
        throw std::runtime_error("Checkpoint all_boards does not match this program. To restart fresh, delete the checkpoint file or specify a different checkpoint file.");
    }
    if (ckpt.current_hand < expected_p1 || ckpt.current_hand > expected_p2 + 1) {
        throw std::runtime_error("Checkpoint current_hand is outside the requested range.");
    }
    if (ckpt.next_board > expected_all_boards) {
        throw std::runtime_error("Checkpoint next_board is past the end of a hand.");
    }

    return true;
}

static void reset_current_hand_checkpoint_state_9p(
    ResultArray& current_totals,
    unsigned long long& total_type_count,
    int& max_type_count_seen,
    unsigned long long& total_dp_states,
    unsigned long long& cache_hits)
{
    current_totals = zero_result_array();
    total_type_count = 0ULL;
    max_type_count_seen = 0;
    total_dp_states = 0ULL;
    cache_hits = 0ULL;
}

int main(int argc, char** argv) {
    try {
        if (argc < 5 || argc > 6) {
            print_usage(argv[0]);
            return 1;
        }

        const int p1 = std::atoi(argv[1]);
        const int p2 = std::atoi(argv[2]);
        const std::string checkpoint_path = argv[3];
        const std::string output_path = argv[4];

        std::cerr << "Program start: p1=" << argv[1]
                  << " p2=" << argv[2]
                  << " checkpoint=" << checkpoint_path
                  << " output_csv=" << output_path << "\n";

        if (p1 < 0 || p1 > 168 || p2 < 0 || p2 > 168 || (p1 > p2)) {
            throw std::runtime_error("p1 and p2 must be hand indexes from 0 to 168 with p1 <= p2.");
        }
        if (checkpoint_path.empty()) {
            throw std::runtime_error("checkpoint_file is mandatory and must not be empty.");
        }
        if (output_path.empty()) {
            throw std::runtime_error("output_csv is mandatory and must not be empty.");
        }

        int chunk_boards = DEFAULT_CHUNK_BOARDS;
        if (argc >= 6) chunk_boards = std::atoi(argv[5]);
        if (chunk_boards < 1) {
            throw std::runtime_error("chunk_boards must be at least 1.");
        }

        double progress_interval_seconds = CHECKPOINT_INTERVAL_SECONDS;
        const char* env_progress = std::getenv("HOLDEM_PROGRESS_SECONDS");
        if (env_progress && std::atof(env_progress) > 0.0) {
            progress_interval_seconds = std::atof(env_progress);
        }

        std::cerr << "Parsed command line: p1=" << p1 << " p2=" << p2
                  << " chunk_boards=" << chunk_boards
                  << " progress_interval_seconds=" << progress_interval_seconds << "\n";

        std::cerr << "Loading HandRanks.dat\n";
        std::vector<int> hr_host = load_handranks("HandRanks.dat");
        if (static_cast<int>(hr_host.size()) != HR_EXPECTED_SIZE) {
            std::cerr << "Warning: HandRanks.dat contains " << hr_host.size()
                      << " integers; expected " << HR_EXPECTED_SIZE
                      << ". Continuing anyway.\n";
        }

        std::cerr << "CPU-only build: no GPU device is used.\n";

        unsigned int cpu_threads = std::thread::hardware_concurrency();
        if (cpu_threads == 0U) cpu_threads = 1U;
        const char* env_threads = std::getenv("HOLDEM_CPU_THREADS");
        if (env_threads && std::atoi(env_threads) > 0) {
            cpu_threads = static_cast<unsigned int>(std::atoi(env_threads));
        }

        size_t board_cache_limit = static_cast<size_t>(DEFAULT_BOARD_CACHE_LIMIT);
        const char* env_cache = std::getenv("HOLDEM_BOARD_CACHE_LIMIT");
        if (env_cache && env_cache[0] != '\0') {
            char* endp = nullptr;
            const unsigned long long parsed = std::strtoull(env_cache, &endp, 10);
            if (endp != env_cache) {
                board_cache_limit = static_cast<size_t>(parsed);
            }
        }

        const unsigned long long all_boards = choose_host(50, 5);
        const U128 expected_per_hand = expected_deals_per_hand_5p(all_boards);
        const std::vector<StartingHandType9> hands = build_169_starting_hand_types_9p();
        bool resumed_from_checkpoint = false;

        int current_hand = p1;
        unsigned long long next_board = 0ULL;
        double previous_elapsed_seconds = 0.0;
        ResultArray current_totals = zero_result_array();
        unsigned long long total_type_count = 0ULL;
        int max_type_count_seen = 0;
        unsigned long long total_dp_states = 0ULL;
        unsigned long long cache_hits = 0ULL;

        Checkpoint9p ckpt;
        if (load_checkpoint_9p(checkpoint_path, p1, p2, output_path, all_boards, ckpt)) {
            current_hand = ckpt.current_hand;
            next_board = ckpt.next_board;
            previous_elapsed_seconds = ckpt.elapsed_seconds;
            current_totals = ckpt.current_totals;
            total_type_count = ckpt.total_type_count;
            max_type_count_seen = ckpt.max_type_count_seen;
            total_dp_states = ckpt.total_dp_states;
            cache_hits = ckpt.cache_hits;
            resumed_from_checkpoint = true;

            std::cerr << "Loaded checkpoint: " << checkpoint_path << "\n";
            std::cerr << "Resuming hand index " << current_hand
                      << ", next board " << next_board
                      << ", accumulated elapsed " << fmt_elapsed(previous_elapsed_seconds)
                      << "\n";
        } else {
            save_checkpoint_9p(checkpoint_path, p1, p2, output_path, all_boards, current_hand,
                               next_board, previous_elapsed_seconds, total_type_count,
                               max_type_count_seen, total_dp_states, cache_hits,
                               current_totals);
            std::cerr << "Created checkpoint: " << checkpoint_path << "\n";
        }

        if (current_hand > p2) {
            std::cerr << "Checkpoint indicates the requested hand range is already complete.\n";
            std::remove(checkpoint_path.c_str());
            return 0;
        }

        const std::ios_base::openmode csv_mode = std::ios::out |
            (resumed_from_checkpoint ? std::ios::app : std::ios::trunc);
        std::ofstream csv(output_path.c_str(), csv_mode);
        if (!csv) {
            throw std::runtime_error("Failed to open output CSV: " + output_path);
        }

        std::cerr << "CPU-only 5-player 169-hand-type MIT production CSV run\n";
        std::cerr << "Program variant: " << PROGRAM_VARIANT_NAME << "\n";
        std::cerr << "Hand range: " << p1 << " through " << p2 << " inclusive\n";
        std::cerr << "Output CSV: " << output_path << "\n";
        std::cerr << "Checkpoint file: " << checkpoint_path << "\n";
        std::cerr << "Progress/checkpoint interval seconds: " << progress_interval_seconds
                  << " (set HOLDEM_PROGRESS_SECONDS to override)\n";
        std::cerr << "Chunk boards: " << chunk_boards << "\n";
        std::cerr << "CPU worker threads: " << cpu_threads << "\n";
        std::cerr << "MIT counter: no recursive DP memo, no board-signature cache, no GPU dependency\n";
        std::cerr << "Boards per hand: " << all_boards << "\n";
        std::cerr << "Expected complete deals per hand: " << u128_to_string(expected_per_hand) << "\n";
        std::cerr << "CSV columns: hand type, hero strict, hero ties 2..5, player 2..5 strict, opponent ties 2..4\n";

        const auto session_t0 = std::chrono::steady_clock::now();
        auto last_checkpoint_save = session_t0;

        while (current_hand <= p2) {
            const StartingHandType9& hand = hands[static_cast<size_t>(current_hand)];
            const int hero0 = parse_tpt_card(hand.card1);
            const int hero1 = parse_tpt_card(hand.card2);
            if (hero0 < 1 || hero1 < 1 || hero0 == hero1) {
                throw std::runtime_error("Internal error: invalid representative hand for " + hand.label);
            }

            std::cerr << "Starting/resuming hand index " << current_hand
                      << " / 168: " << hand.label << " (" << hand.card1
                      << ' ' << hand.card2 << "), next board " << next_board << "\n";

            std::vector<unsigned char> reduced52;
            reduced52.reserve(52);
            for (int c = 1; c <= 52; ++c) {
                if (c != hero0 && c != hero1) {
                    reduced52.push_back(static_cast<unsigned char>(c));
                }
            }
            reduced52.push_back(static_cast<unsigned char>(hero0));
            reduced52.push_back(static_cast<unsigned char>(hero1));
            if (reduced52.size() != 52U) {
                throw std::runtime_error("Internal reduced deck construction failed for " + hand.label);
            }

            std::vector<unsigned short> h_hero_ranks(static_cast<size_t>(chunk_boards));
            std::vector<unsigned short> h_edge_ranks(static_cast<size_t>(chunk_boards) * EDGE_COUNT);

            std::unordered_map<std::string, BoardCacheEntry> board_cache;
            if (board_cache_limit > 0) {
                board_cache.reserve(std::min<size_t>(board_cache_limit, static_cast<size_t>(65536)));
            }
            board_cache.max_load_factor(0.7f);
            std::mutex board_cache_mutex;

            const auto hand_t0 = std::chrono::steady_clock::now();

            while (next_board < all_boards) {
                const int this_chunk = static_cast<int>(
                    std::min<unsigned long long>(static_cast<unsigned long long>(chunk_boards), all_boards - next_board));

                rank_boards_cpu(
                    hr_host.data(),
                    reduced52.data(),
                    next_board,
                    this_chunk,
                    h_hero_ranks.data(),
                    h_edge_ranks.data());

                const unsigned int workers = std::min<unsigned int>(cpu_threads, static_cast<unsigned int>(this_chunk));
                std::vector<ChunkThreadStats> thread_stats(workers);
                std::vector<std::thread> worker_threads;
                worker_threads.reserve(workers);
                std::atomic<bool> worker_failed(false);
                std::mutex worker_error_mutex;
                std::string worker_error;

                for (unsigned int t = 0; t < workers; ++t) {
                    worker_threads.emplace_back([&, t]() {
                        try {
                            MitBoardCounter mit_counter;

                            for (int b = static_cast<int>(t); b < this_chunk; b += static_cast<int>(workers)) {
                                if (worker_failed.load()) {
                                    break;
                                }
                                const unsigned short* erow =
                                    h_edge_ranks.data() + static_cast<size_t>(b) * EDGE_COUNT;
                                const unsigned short h_rank = h_hero_ranks[b];

                                ResultArray br = mit_counter.compute(h_rank, erow);

                                thread_stats[t].total_type_count += mit_counter.last_unique_ranks;
                                thread_stats[t].max_type_count = std::max(
                                    thread_stats[t].max_type_count,
                                    static_cast<int>(mit_counter.last_unique_ranks));
                                thread_stats[t].dp_states += 148995ULL; // one MIT four-card-set pass unit per board

                                for (int i = 0; i < CATEGORY_COUNT; ++i) {
                                    u128_add_inplace(thread_stats[t].totals[i], br[i]);
                                }

                                ++thread_stats[t].boards_done;
                            }
                        } catch (const std::exception& ex) {
                            worker_failed.store(true);
                            std::ostringstream oss;
                            oss << "WORKER THREAD EXCEPTION t=" << t
                                << " message=" << ex.what();
                            {
                                std::lock_guard<std::mutex> lock(worker_error_mutex);
                                if (worker_error.empty()) worker_error = oss.str();
                            }
                            std::cerr << oss.str() << "\n";
                        } catch (...) {
                            worker_failed.store(true);
                            std::ostringstream oss;
                            oss << "WORKER THREAD UNKNOWN EXCEPTION t=" << t;
                            {
                                std::lock_guard<std::mutex> lock(worker_error_mutex);
                                if (worker_error.empty()) worker_error = oss.str();
                            }
                            std::cerr << oss.str() << "\n";
                        }
                    });
                }

                for (std::thread& th : worker_threads) {
                    th.join();
                }

                if (!worker_error.empty()) {
                    throw std::runtime_error(worker_error);
                }

                unsigned long long chunk_boards_done = 0ULL;
                for (const ChunkThreadStats& st : thread_stats) {
                    for (int i = 0; i < CATEGORY_COUNT; ++i) {
                        u128_add_inplace(current_totals[i], st.totals[i]);
                    }
                    chunk_boards_done += st.boards_done;
                    total_type_count += st.total_type_count;
                    max_type_count_seen = std::max(max_type_count_seen, st.max_type_count);
                    total_dp_states += st.dp_states;
                    cache_hits += st.cache_hits;
                }

                next_board += chunk_boards_done;
                if (chunk_boards_done == 0ULL) {
                    throw std::runtime_error("Internal error: chunk completed zero boards.");
                }
                const auto now = std::chrono::steady_clock::now();
                const double session_elapsed = std::chrono::duration<double>(now - session_t0).count();
                const double accumulated_elapsed = previous_elapsed_seconds + session_elapsed;
                const double hand_pct = 100.0 * static_cast<double>(next_board) / static_cast<double>(all_boards);
                const double avg_types = next_board
                    ? static_cast<double>(total_type_count) / static_cast<double>(next_board)
                    : 0.0;

                const double seconds_since_checkpoint =
                    std::chrono::duration<double>(now - last_checkpoint_save).count();
                if (seconds_since_checkpoint >= progress_interval_seconds) {
                    save_checkpoint_9p(checkpoint_path, p1, p2, output_path, all_boards, current_hand,
                                       next_board, accumulated_elapsed, total_type_count,
                                       max_type_count_seen, total_dp_states, cache_hits,
                                       current_totals);
                    last_checkpoint_save = now;

                    const long double total_range_boards =
                        static_cast<long double>(p2 - p1 + 1) * static_cast<long double>(all_boards);
                    const long double completed_range_boards =
                        static_cast<long double>(current_hand - p1) * static_cast<long double>(all_boards) +
                        static_cast<long double>(next_board);
                    const long double remaining_range_boards =
                        (completed_range_boards < total_range_boards)
                            ? (total_range_boards - completed_range_boards)
                            : 0.0L;
                    const double range_pct = total_range_boards > 0.0L
                        ? static_cast<double>(100.0L * completed_range_boards / total_range_boards)
                        : 100.0;
                    const double boards_per_second = (accumulated_elapsed > 0.0 && completed_range_boards > 0.0L)
                        ? static_cast<double>(completed_range_boards / static_cast<long double>(accumulated_elapsed))
                        : 0.0;
                    const double remaining_seconds = (boards_per_second > 0.0)
                        ? static_cast<double>(remaining_range_boards / static_cast<long double>(boards_per_second))
                        : -1.0;
                    const std::string remaining_text =
                        (remaining_seconds >= 0.0) ? fmt_elapsed(remaining_seconds) : std::string("unknown");
                    const std::string total_runtime_text =
                        (remaining_seconds >= 0.0) ? fmt_elapsed(accumulated_elapsed + remaining_seconds) : std::string("unknown");

                    std::cerr << "Progress/checkpoint: hand " << current_hand << " (" << hand.label << ") "
                              << next_board << " / " << all_boards
                              << " boards in current hand (" << std::fixed << std::setprecision(2) << hand_pct << "%)"
                              << ", requested range " << std::setprecision(4) << range_pct << "%"
                              << ", elapsed " << fmt_elapsed(accumulated_elapsed)
                              << ", remaining " << remaining_text
                              << ", estimated total runtime " << total_runtime_text
                              << ", rate " << std::setprecision(2) << boards_per_second << " boards/sec"
                              << ", avg unique ranks " << std::setprecision(2) << avg_types
                              << ", max unique ranks " << max_type_count_seen
                              << "\n";
                }
            }


            const int base = HOST_CAT_BASE[5];
            U128 total = u128_zero();
            for (int c = 0; c < 9; ++c) {
                u128_add_inplace(total, current_totals[base + c]);
            }
            if (u128_to_string(total) != u128_to_string(expected_per_hand)) {
                std::ostringstream oss;
                oss << "Total mismatch for " << hand.label
                    << ": got " << u128_to_string(total)
                    << ", expected " << u128_to_string(expected_per_hand);
                throw std::runtime_error(oss.str());
            }

            write_csv_row_5p(csv, hand.label, current_totals);
            csv.flush();

            const auto hand_t1 = std::chrono::steady_clock::now();
            const double hand_elapsed = std::chrono::duration<double>(hand_t1 - hand_t0).count();
            const double session_elapsed_at_hand_end = std::chrono::duration<double>(hand_t1 - session_t0).count();
            const double accumulated_elapsed_at_hand_end = previous_elapsed_seconds + session_elapsed_at_hand_end;
            {
                const long double total_range_boards =
                    static_cast<long double>(p2 - p1 + 1) * static_cast<long double>(all_boards);
                const long double completed_range_boards =
                    static_cast<long double>(current_hand - p1 + 1) * static_cast<long double>(all_boards);
                const long double remaining_range_boards =
                    (completed_range_boards < total_range_boards)
                        ? (total_range_boards - completed_range_boards)
                        : 0.0L;
                const double range_pct = total_range_boards > 0.0L
                    ? static_cast<double>(100.0L * completed_range_boards / total_range_boards)
                    : 100.0;
                const double boards_per_second =
                    (accumulated_elapsed_at_hand_end > 0.0 && completed_range_boards > 0.0L)
                    ? static_cast<double>(completed_range_boards / static_cast<long double>(accumulated_elapsed_at_hand_end))
                    : 0.0;
                const double remaining_seconds = (boards_per_second > 0.0)
                    ? static_cast<double>(remaining_range_boards / static_cast<long double>(boards_per_second))
                    : -1.0;
                const std::string remaining_text =
                    (remaining_seconds >= 0.0) ? fmt_elapsed(remaining_seconds) : std::string("unknown");
                std::cerr << "Completed hand " << current_hand << " (" << hand.label << ")"
                          << ", hand runtime this session " << fmt_elapsed(hand_elapsed)
                          << ", accumulated runtime " << fmt_elapsed(accumulated_elapsed_at_hand_end)
                          << ", requested range " << std::fixed << std::setprecision(4) << range_pct << "%"
                          << ", estimated remaining " << remaining_text
                          << "\n";
            }

            ++current_hand;
            next_board = 0ULL;
            reset_current_hand_checkpoint_state_9p(
                current_totals, total_type_count, max_type_count_seen,
                total_dp_states, cache_hits);

            const auto after_hand = std::chrono::steady_clock::now();
            const double session_elapsed = std::chrono::duration<double>(after_hand - session_t0).count();
            const double accumulated_elapsed = previous_elapsed_seconds + session_elapsed;
            save_checkpoint_9p(checkpoint_path, p1, p2, output_path, all_boards, current_hand,
                               next_board, accumulated_elapsed, total_type_count,
                               max_type_count_seen, total_dp_states, cache_hits,
                               current_totals);
            last_checkpoint_save = after_hand;
        }

        std::cerr << "Completed requested hand range " << p1 << " through " << p2 << ".\n";
        std::cerr << "Wrote CSV rows to: " << output_path << "\n";
        std::remove(checkpoint_path.c_str());
        std::cerr << "Removed checkpoint after successful completion: " << checkpoint_path << "\n";
        return 0;
    } catch (const std::bad_alloc& ex) {
        std::cerr << "Fatal bad_alloc: " << ex.what() << "\n";
        return 2;
    } catch (const std::exception& ex) {
        std::cerr << "Error: " << ex.what() << "\n";
        return 1;
    } catch (...) {
        std::cerr << "Fatal unknown exception.\n";
        return 3;
    }
}
