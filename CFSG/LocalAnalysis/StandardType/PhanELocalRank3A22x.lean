module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A22xHyp
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsLink
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsNbr
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsCone

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem a3_22x_models (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((flagSys K 3).restrict (set22x K f)).Connected ∧
      ((flagSys K 3).restrict (set22x K f)).SimplyTwoConnected := by
  have h := clsHyp_a3_22x f hK hq
  rw [genSet_a3_22x_eq f]
  exact admSet_simplyTwoConnected (AdmS (D22x (K := K) f)) (cls_fibreConn _ h)
    (cls_commonNbr _ h) (cls_coneTri _ h)

end CFSG.ClassicalInvolution.Phan.PhanE

end
