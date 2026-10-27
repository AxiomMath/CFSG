module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A121BaseB
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A121BaseC
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsTLink
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsTNbr
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsTCone

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem a3_121_models (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((flagSys K 3).restrict (genSet K f 4 [0, 1, 3, 4] [])).Connected ∧
      ((flagSys K 3).restrict (genSet K f 4 [0, 1, 3, 4] [])).SimplyTwoConnected := by
  have hbase : TBase (D121 (K := K) f) :=
    ⟨a121_link f hK hq, (a121_nbr f hK hq).1, (a121_nbr f hK hq).2.1, (a121_nbr f hK hq).2.2,
      a121_cone f hK hq⟩
  rw [genSet_a3_121_eq f, admSet_a3_121_eq f hK]
  exact admSet_simplyTwoConnected_weak (AdmT (D121 (K := K) f)) (clsT_fibreConn _ hbase)
    (clsT_commonNbrW _ hbase) (clsT_coneTri _ hbase)

end CFSG.ClassicalInvolution.Phan.PhanE

end
