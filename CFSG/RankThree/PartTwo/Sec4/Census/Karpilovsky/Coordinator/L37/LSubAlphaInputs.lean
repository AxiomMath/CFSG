module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocksInputs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

open CFSG.KC.Misc.F7 CFSG.KC.Loop CFSG.RankThree.Native.ONTriple

@[expose] noncomputable def alphaPts : List Nat :=
  [nat_lit 73367, nat_lit 63320, nat_lit 20519, nat_lit 30329, nat_lit 645, nat_lit 31125,
    nat_lit 86937, nat_lit 36434, nat_lit 85904]

@[expose] noncomputable def alphaRows : List (List Nat) :=
  [[nat_lit 0, nat_lit 0], [nat_lit 0, nat_lit 1], [nat_lit 0, nat_lit 2], [nat_lit 1, nat_lit 0],
    [nat_lit 1, nat_lit 1], [nat_lit 1, nat_lit 2], [nat_lit 2, nat_lit 0], [nat_lit 2, nat_lit 1],
    [nat_lit 2, nat_lit 2]]

@[expose] noncomputable def vRegA (m i : Nat) : Nat := nthN (nthLN (rV.getD 1 []) m) i

@[expose] noncomputable def fixXOK (w n v : Nat) : Bool :=
  inSpan8 (imgS (imgS (f7Img (ptCode w) (revM (rIM n))) (rIM v)) (rM n)) (widenF (ptCode w))
    (ptPw w)

@[expose] noncomputable def alphaOK (k : Nat) : Bool :=
  andB (Nat.blt (nthN alphaPts k) nPt) (allN 2 fun l => allN 2 fun i =>
    fixXOK (nthN alphaPts k) (nthN (nthLN rL 1) l) (vRegA (nthN (nthLN alphaRows k) l) i))

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
