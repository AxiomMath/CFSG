module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45Inputs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q

open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
  CFSG.ComponentClassification.J2Cover

@[expose] def j2VArr (j : ℕ) : Array ℕ := vkArr (j / 2) (j % 2 + 1)

@[expose] def j2VProd : List ℕ → Array ℕ
  | [] => idA 315
  | j :: w => compA 315 (j2VArr j) (j2VProd w)

@[expose] def j2VWordA : List ℕ := [1, 0, 4, 2, 0, 3, 0, 4, 1, 0]

@[expose] def j2VWordB : List ℕ := [3, 5, 1, 4, 3, 4, 3, 0, 3, 0]

@[expose] def j2VGenCheck : Bool :=
  (j2VWordA ++ j2VWordB).all (fun j => decide (j < 6)) &&
    eqA 315 (j2VProd j2VWordA) autStrong[0]! && eqA 315 (j2VProd j2VWordB) autStrong[1]!

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q
