module

public import CFSG.LocalAnalysis.StandardType.PhanELocalClsTD
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsTLink
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A13pBase

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem a3_13p_models (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((flagSys K 3).restrict (genSet K f 4 [0, 1, 4] [false, true])).Connected ∧
      ((flagSys K 3).restrict (genSet K f 4 [0, 1, 4] [false, true])).SimplyTwoConnected := by
  rw [genSet_a3_13p_eq f, ← admT_D13p f]
  exact admSet_simplyTwoConnected_diag (AdmT (D13p (K := K) f))
    (clsT_fibreConn_of_link _ (D13p_link f hK hq))
    (clsT_commonNbrD _ (D13p_nbr2 f hK hq) (D13p_nbr4 f hK hq) (D13p_nbr3 f hK hq))
    (clsT_coneTriD _ (D13p_cone f hK))

end CFSG.ClassicalInvolution.Phan.PhanE

end
