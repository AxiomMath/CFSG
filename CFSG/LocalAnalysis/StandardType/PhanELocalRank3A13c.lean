module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A13cBaseB
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsTLink
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsTNbr
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsTCone

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem a3_13c_models (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((flagSys K 3).restrict (genSet K f 4 [0, 1, 4] [])).Connected ∧
      ((flagSys K 3).restrict (genSet K f 4 [0, 1, 4] [])).SimplyTwoConnected := by
  have hbase : TBase (D13c (K := K) f) :=
    ⟨a13c_link f hK hq, (a13c_nbr f hK hq).1, (a13c_nbr f hK hq).2.1, (a13c_nbr f hK hq).2.2,
      a13c_cone f hK hq⟩
  rw [genSet_a3_13c_eq f, admSet_a3_13c_eq f hK]
  exact admSet_simplyTwoConnected_weak (AdmT (D13c (K := K) f)) (clsT_fibreConn _ hbase)
    (clsT_commonNbrW _ hbase) (clsT_coneTri _ hbase)

end CFSG.ClassicalInvolution.Phan.PhanE

end
