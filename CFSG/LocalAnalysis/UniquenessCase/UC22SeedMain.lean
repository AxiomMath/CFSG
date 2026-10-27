module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SeedT
public import CFSG.LocalAnalysis.UniquenessCase.UC22SeedE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

theorem k339SeedBridge : K339SeedBridge := by
  intro S _ _ _ hcent H _ _ ι hG hnc
  obtain ⟨k, _, _, _, π, T, hT, hset⟩ := exists_seedSetting hG
  have hnc' : ⁅(⊤ : Subgroup H), quasithinOmegaOneCenter (T : Subgroup H)⁆ ≠ ⊥ := by
    rw [hT]
    exact seed_hnc hG.injective hnc
  have hJ' : omegaOneCenterOf (thompsonJ (T : Subgroup H)) ≤
      Subgroup.centralizer ((T : Subgroup H) : Set H) := by
    rw [hT]
    exact seed_hJ hG.injective hcent
  obtain ⟨F, hF, hFin, ρ, ψ, hseed⟩ := exists_isSeed_of_setting hset hnc' hJ' T rfl
  exact ⟨F, hF, hFin, T, ρ, ψ, hT, hseed⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
