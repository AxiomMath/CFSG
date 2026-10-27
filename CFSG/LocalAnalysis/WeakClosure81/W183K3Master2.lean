module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Leaves
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Master2Rk2
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Master2Rk3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

theorem br3MasterTwo_holds : Br3MasterTwo := by
  intro rows V _ _ _ Y T L₁ L₂ Γ VA 𝒢 Zs m i₀ δ ED hc htwo hshape hZ hτ hne hall hED
  by_cases hrk : ∀ D ∈ Γ, 3 ≤ mRank D
  · exact w183k3m2_false_of_rank_three rows hc htwo hshape hZ hall hne hrk hED
  · obtain ⟨D₀, hD₀not⟩ := not_forall.1 hrk
    have hD₀ : D₀ ∈ Γ := by
      by_contra h
      exact hD₀not (fun hmem => absurd hmem h)
    have hlt : ¬ 3 ≤ mRank D₀ := fun h => hD₀not (fun _ => h)
    have hrank : mRank D₀ = 2 := by have := hall D₀ hD₀; omega
    exact w183k3m2_false_of_rank_two rows hc htwo hshape hZ hτ hall hD₀ hrank

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
