module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A22pHyp
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsLink
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsNbr
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsCone

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem a3_22p_models (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((flagSys K 3).restrict (genSet K f 4 [0, 2, 4] [])).Connected ∧
      ((flagSys K 3).restrict (genSet K f 4 [0, 2, 4] [])).SimplyTwoConnected := by
  have h := clsHyp_a3_22p f hK hq
  rw [genSet_a3_22p_eq f]
  exact admSet_simplyTwoConnected (AdmS (D22p (K := K) f)) (cls_fibreConn _ h)
    (cls_commonNbr _ h) (cls_coneTri _ h)

end CFSG.ClassicalInvolution.Phan.PhanE

end
