module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12SigCheckInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q

open CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12
  CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig

@[expose] def m12VWordA : List (ℕ × Idx) :=
  [(2, (10, 10, 4, 6, 1)), (0, (3, 10, 0, 0, 5)), (1, (6, 0, 4, 6, 3)), (2, (10, 10, 4, 6, 1)),
    (1, (11, 6, 7, 4, 0)), (0, (4, 4, 9, 3, 6))]

@[expose] def m12VWordB : List (ℕ × Idx) :=
  [(0, (3, 10, 0, 0, 5)), (2, (10, 10, 4, 6, 1)), (1, (6, 0, 4, 6, 3)), (0, (8, 9, 0, 3, 6)),
    (2, (7, 9, 3, 4, 6)), (1, (5, 9, 2, 7, 4)), (0, (8, 9, 0, 3, 6))]

@[expose] def m12VProd (L : List (ℕ × Idx)) : List ℕ :=
  L.foldr (fun p t => tmul (prodT p.2) t) tid

@[expose] def m12VGenCheck : Bool :=
  ((m12VWordA ++ m12VWordB).all fun p => decide (p.1 < 3) && (idxV p.1).contains p.2) &&
    m12VProd m12VWordA == tA && m12VProd m12VWordB == tB

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q
