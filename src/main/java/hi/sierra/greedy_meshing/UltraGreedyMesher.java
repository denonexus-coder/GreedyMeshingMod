package hi.sierra.greedy_meshing;

import net.minecraft.core.Direction;
import net.minecraft.world.level.block.state.BlockState;

import java.util.BitSet;
import java.util.List;

/*
 * ULTRA GREEDY MESHER V4 — MÁXIMA PERFORMANCE (Java 17)
 *
 * Otimizações sobre o GreedyMesher original:
 *   - Saída em buffer primitivo SoA (QuadBuffer) — nenhum GreedyQuad alocado durante a varredura
 *   - Nenhum ArrayList por seção — QuadBuffer reusado via ThreadLocal
 *   - Multi-thread: processa N seções em paralelo nos núcleos disponíveis
 *   - Índices lineares, pure bitwise, sem packing/unpacking no loop quente
 *   - Zero alocação de objetos no caminho quente de varredura
 *   - Sem System.gc()
 *   - Compatível com Java 17
 */
public final class UltraGreedyMesher {

    public static final int SECTION_SIZE = GreedyMesher.SECTION_SIZE;
    public static final int TOTAL_BLOCKS = GreedyMesher.TOTAL_BLOCKS;
    private static final Direction[] ALL_FACES = Direction.values();

    private static final ThreadLocal<QuadBuffer> QUAD_TL = ThreadLocal.withInitial(QuadBuffer::new);

    private UltraGreedyMesher() {}

    /* =====================================================================
     *  QUAD BUFFER — saída primitiva SoA (estrutura de arrays, não de objetos)
     * ===================================================================== */
    public static final class QuadBuffer {
        public int[] face;
        public int[] x;
        public int[] y;
        public int[] z;
        public int[] w;
        public int[] h;
        public int[] stateIdx;
        public int size;
        public int capacity;

        public QuadBuffer() {
            this(256);
        }

        public QuadBuffer(int capacity) {
            this.capacity = capacity;
            this.face = new int[capacity];
            this.x = new int[capacity];
            this.y = new int[capacity];
            this.z = new int[capacity];
            this.w = new int[capacity];
            this.h = new int[capacity];
            this.stateIdx = new int[capacity];
            this.size = 0;
        }

        public void ensureCapacity(int need) {
            if (need > capacity) {
                int nc = capacity;
                while (nc < need) nc <<= 1;
                face = java.util.Arrays.copyOf(face, nc);
                x = java.util.Arrays.copyOf(x, nc);
                y = java.util.Arrays.copyOf(y, nc);
                z = java.util.Arrays.copyOf(z, nc);
                w = java.util.Arrays.copyOf(w, nc);
                h = java.util.Arrays.copyOf(h, nc);
                stateIdx = java.util.Arrays.copyOf(stateIdx, nc);
                capacity = nc;
            }
        }

        public void add(int face, int x, int y, int z, int w, int h, int stateIdx) {
            if (size >= capacity) ensureCapacity(size + 1);
            this.face[size] = face;
            this.x[size] = x;
            this.y[size] = y;
            this.z[size] = z;
            this.w[size] = w;
            this.h[size] = h;
            this.stateIdx[size] = stateIdx;
            size++;
        }

        public void reset() {
            size = 0;
        }
    }

    /* =====================================================================
     *  MESH ULTRA — seção única, zero alloc na varredura, escrita direta em QuadBuffer
     * ===================================================================== */
    public static void meshUltra(
            BlockState[] blocks,
            BitSet[] faceMasks,
            long[][] mergeKeys,
            QuadBuffer out) {

        out.reset();
        BinarySweepState bw = GreedyMesher.BIN_SWEEP_TL.get();
        int[] rows = bw.rows;
        long[] keys = bw.keys;
        int[] origins = bw.origins;
        int[] depthCells = bw.depthCells;
        int[] depthCounts = bw.depthCounts;

        for (Direction dir : ALL_FACES) {
            int fi = dir.ordinal();
            BitSet visible = faceMasks[fi];
            if (visible.isEmpty()) continue;

            long[] faceKeys = mergeKeys[fi];
            int[][] table = GreedyMesher.SWEEP_TO_BLOCK[fi];
            int[] inverse = GreedyMesher.BLOCK_TO_SWEEP[fi];

            java.util.Arrays.fill(depthCounts, 0);
            for (int bi = visible.nextSetBit(0); bi >= 0; bi = visible.nextSetBit(bi + 1)) {
                if (blocks[bi] == null) continue;
                int depth = inverse[bi] >>> 8;
                depthCells[(depth << 8) + depthCounts[depth]++] = bi;
            }

            for (int depth = 0; depth < SECTION_SIZE; depth++) {
                int cellCount = depthCounts[depth];
                if (cellCount == 0) continue;

                int[] lookup = table[depth];
                int cellBase = depth << 8;
                int nGroups = 0;
                int lastGid = -1;

                for (int c = 0; c < cellCount; c++) {
                    int bi = depthCells[cellBase + c];
                    BlockState block = blocks[bi];
                    int packed = inverse[bi];
                    int row = (packed >>> 4) & 0xF;
                    int col = packed & 0xF;

                    long ck = ((long) System.identityHashCode(block) << 32) | (faceKeys[bi] & 0xFFFFFFFFL);
                    int gid = -1;
                    if (lastGid >= 0 && keys[lastGid] == ck) {
                        gid = lastGid;
                    } else {
                        for (int g = 0; g < nGroups; g++) {
                            if (keys[g] == ck) { gid = g; break; }
                        }
                    }
                    if (gid == -1) {
                        if (nGroups >= BinarySweepState.CAP) {
                            continue;
                        }
                        gid = nGroups++;
                        keys[gid] = ck;
                        origins[gid] = bi;
                        for (int r = 0; r < SECTION_SIZE; r++) rows[gid * SECTION_SIZE + r] = 0;
                    }
                    lastGid = gid;
                    rows[gid * SECTION_SIZE + row] |= 1 << col;
                }

                for (int g = 0; g < nGroups; g++) {
                    int base = g * SECTION_SIZE;
                    BlockState block = blocks[origins[g]];
                    int stateIdx = origins[g]; // índice direto no array blocks[]

                    for (int row = 0; row < SECTION_SIZE; row++) {
                        int bits = rows[base + row];
                        while (bits != 0) {
                            int col = Integer.numberOfTrailingZeros(bits);
                            int w = Integer.numberOfTrailingZeros(~(bits >>> col));
                            int span = ((1 << w) - 1) << col;

                            int hh = 1;
                            while (row + hh < SECTION_SIZE
                                    && (rows[base + row + hh] & span) == span) hh++;

                            for (int dr = 0; dr < hh; dr++) rows[base + row + dr] &= ~span;

                            int qi = lookup[row * SECTION_SIZE + col];
                            out.add(fi,
                                    qi & 0xF, (qi >> 8) & 0xF, (qi >> 4) & 0xF,
                                    w, hh, stateIdx);

                            bits = rows[base + row];
                        }
                    }
                }
            }
        }
    }

    /* =====================================================================
     *  MESH ULTRA MT — múltiplas seções em paralelo (multi-thread)
     * ===================================================================== */
    public static void meshUltraMT(
            BlockState[][] blocksSections,
            BitSet[][] faceMasksSections,
            long[][][] mergeKeysSections,
            QuadBuffer[] outBuffers,
            int sectionCount) {

        if (sectionCount <= 0) return;

        int cores = Runtime.getRuntime().availableProcessors();
        int numThreads = Math.max(1, Math.min(cores, 8));
        int perThread = (sectionCount + numThreads - 1) / numThreads;

        Thread[] threads = new Thread[numThreads];
        for (int t = 0; t < numThreads; t++) {
            final int threadId = t;
            threads[t] = new Thread(() -> {
                int start = threadId * perThread;
                int end = Math.min(start + perThread, sectionCount);
                for (int s = start; s < end; s++) {
                    meshUltra(
                            blocksSections[s],
                            faceMasksSections[s],
                            mergeKeysSections[s],
                            outBuffers[s]);
                }
            }, "UGM-" + t);
            threads[t].start();
        }

        for (Thread th : threads) {
            try {
                th.join();
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
    }

    /* =====================================================================
     *  BACKWARD COMPAT — QuadBuffer → List<GreedyQuad>
     * ===================================================================== */
    public static void toQuadList(
            QuadBuffer buffer,
            BlockState[] states,
            List<GreedyMesher.GreedyQuad> out) {

        for (int i = 0; i < buffer.size; i++) {
            out.add(new GreedyMesher.GreedyQuad(
                    Direction.values()[buffer.face[i]],
                    buffer.x[i], buffer.y[i], buffer.z[i],
                    buffer.w[i], buffer.h[i],
                    states[buffer.stateIdx[i]]));
        }
    }

    /* =====================================================================
     *  THREAD-LOCAL QUAD BUFFER (reuso entre seções)
     * ===================================================================== */
    public static QuadBuffer acquireQuadBuffer() {
        return QUAD_TL.get();
    }
}
