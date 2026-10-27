module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Open

theorem spCenter_trivial {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (z : ↥(StatedSp m K)) (hz : ∀ h : ↥(StatedSp m K), z * h = h * z) : z = 1 := by
  have hc := CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := K) (m := m)
  have hzmem : z ∈ Subgroup.center ↥(StatedSp m K) :=
    Subgroup.mem_center_iff.2 fun h => (hz h).symm
  rw [hc, Subgroup.mem_bot] at hzmem
  exact hzmem

end S2MathAs3_1619Final

end
