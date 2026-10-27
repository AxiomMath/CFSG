module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A4cLink
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A4cNbr
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A4cCone

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem a3_4c_models (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((flagSys K 3).restrict (genSet K f 4 [0, 4] [false])).Connected ∧
      ((flagSys K 3).restrict (genSet K f 4 [0, 4] [false])).SimplyTwoConnected := by
  rw [genSet_a3_4c_eq f]
  exact admSet_simplyTwoConnected_weak (Adm4c (K := K) f) (adm4c_fibreConn f hK)
    (adm4c_commonNbrW f hK hq) (adm4c_coneTri f hK hq)

end CFSG.ClassicalInvolution.Phan.PhanE

end
