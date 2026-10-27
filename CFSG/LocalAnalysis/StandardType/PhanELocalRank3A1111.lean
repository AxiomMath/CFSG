module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A1111Link
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A1111Nbr
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A1111Cone

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem a3_1111_models (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((flagSys K 3).restrict (genSet K f 4 [0, 1, 2, 3, 4] [])).Connected ∧
      ((flagSys K 3).restrict (genSet K f 4 [0, 1, 2, 3, 4] [])).SimplyTwoConnected := by
  have hQ : 16 ≤ Nat.card K := by
    rw [hK]
    nlinarith [hq]
  rw [genSet_a3_1111_eq (K := K) f]
  exact admSet_simplyTwoConnected (Adm1111 (K := K)) (adm1111_fibreConn hQ)
    (adm1111_commonNbr hQ) (adm1111_coneTri hQ)

end CFSG.ClassicalInvolution.Phan.PhanE

end
