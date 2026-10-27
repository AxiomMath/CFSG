module

public import Certificates.Data.Kernel.D43.TreeDisj
public import Certificates.Kernel.D43.Tree3Data
public import Certificates.Kernel.D43.HexG

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43 CFSG.KC.Enum

@[expose] noncomputable def mem3 (ℓ o s q : Nat) : Bool :=
  strictB (posAt T3Q ℓ q) fun u => bAnd(Nat.blt u s, Nat.beq (ptAt T3R o u) q)

theorem tree3Small : (treeChunk GX.F TW T3R T3Q 0 0 84 6 131069 0 &&
    treeChunk GX.F TW T3R T3Q 2 6888 4 0 131070 0 &&
    treeChunk GX.F TW T3R T3Q 3 6892 324 186 131070 0 &&
    treeChunk GX.F TW T3R T3Q 3 6892 324 186 131070 1 &&
    treeChunk GX.F TW T3R T3Q 5 33460 3 6 131040 0 &&
    treeChunk GX.F TW T3R T3Q 6 33463 81 186 131040 0 &&
    treeChunk GX.F TW T3R T3Q 7 33544 243 479 131040 0) = true := by
  decide +kernel

theorem disj3Small : (disjChunk T3R 0 84 T3R T3Q 1 84 6804 0 &&
    disjChunk T3R 0 84 TR TQ 1 26572 19683 0 &&
    disjChunk T3R 6892 324 T3R T3Q 4 7216 26244 0 &&
    disjChunk T3R 6892 324 T3R T3Q 4 7216 26244 1 &&
    disjChunk T3R 33460 3 T3R T3Q 6 33463 81 0 &&
    disjChunk T3R 33544 243 T3R T3Q 8 33787 6561 0) = true := by
  decide +kernel

theorem mem3All : (mem3 0 0 84 186 && mem3 1 84 6804 15916 && mem3 2 6888 4 1 &&
    mem3 2 6888 4 2 && mem3 2 6888 4 6 && mem3 5 33460 3 1 && mem3 5 33460 3 2) = true := by
  decide +kernel

end CertificateChecks.KernelD43
