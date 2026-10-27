module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Master2Aux
public import CFSG.LocalAnalysis.WeakClosure81.W183K3CoreSetting
public import CFSG.LocalAnalysis.WeakClosure81.W183K3I2
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Alpha

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

private theorem w183k3m2r2_alpha_left (rows : Br3Rows)
    (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (htwo : Br3TwoComp Y T L₁ L₂)
    (hshape : IsAlt (↥L₁ ⧸ Subgroup.center ↥L₁) 6 ∨ IsL3 (↥L₁ ⧸ Subgroup.center ↥L₁) 2)
    (hτ : ∃ τ ∈ T, ActsOnDynkinMod (quasiCentre L₁) L₁ τ)
    (hall : ∀ D ∈ Γ, 2 ≤ mRank D) {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ)
    (hcard : Nat.card ↥D = 4)
    (hker₁ : D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥)
    (hcent₂ : D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))) : False := by
  have hi : 2 ≤ m - i₀ - 1 := by have := hc.hmi; omega
  have hrank : mRank D ≤ m - i₀ - 1 := by
    have h2 : mRank D = 2 := by rw [mRank, hcard]; norm_num
    omega
  have hτY : ∃ τ ∈ Y, ActsOnDynkinMod (quasiCentre L₁) L₁ τ := by
    obtain ⟨τ, hτT, hτd⟩ := hτ
    exact ⟨τ, hc.sylow.1 hτT, hτd⟩
  exact br3_alpha_false rows hc.h131 hc.vfix htwo hD hrank hcard
    (w183k3m2_mem_normalizer hc htwo hall hD).1 hker₁ hcent₂ hshape.symm hτY

theorem w183k3m2_false_of_alpha_config (rows : Br3Rows)
    (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (htwo : Br3TwoComp Y T L₁ L₂)
    (hshape : IsAlt (↥L₁ ⧸ Subgroup.center ↥L₁) 6 ∨ IsL3 (↥L₁ ⧸ Subgroup.center ↥L₁) 2)
    (hτ : ∃ τ ∈ T, ActsOnDynkinMod (quasiCentre L₁) L₁ τ)
    (hall : ∀ D ∈ Γ, 2 ≤ mRank D) {A : Subgroup (LGL 2 V)} (hA : A ∈ Γ)
    (hcard : Nat.card ↥A = 4)
    (hconfig : (A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥ ∧
        A ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ∨
      (A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) = ⊥ ∧
        A ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)))) : False := by
  rcases hconfig with ⟨hker₁, hcent₂⟩ | ⟨hker₂, hcent₁⟩
  · exact w183k3m2r2_alpha_left rows hc htwo hshape hτ hall hA hcard hker₁ hcent₂
  · obtain ⟨x, hxT, hxL⟩ := htwo.swap
    have hxY : x ∈ Y := hc.sylow.1 hxT
    have hxL₂ : cj x L₂ = L₁ := by
      rcases htwo.perm x hxY with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd (h1.symm.trans hxL) htwo.ne
      · exact h2
    have hcard' : Nat.card (cj x A) = 4 := by
      rw [cj, Subgroup.card_map_of_injective (MulAut.conj x).injective]
      exact hcard
    have hker₁' : cj x A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥ := by
      have hmap : Subgroup.centralizer (L₁ : Set (LGL 2 V)) =
          (Subgroup.centralizer (L₂ : Set (LGL 2 V))).map (MulAut.conj x).toMonoidHom := by
        rw [w183k3m2_centralizer_cj x L₂, hxL₂]
      rw [hmap, cj, ← Subgroup.map_inf A (Subgroup.centralizer (L₂ : Set (LGL 2 V)))
        (MulAut.conj x).toMonoidHom (MulAut.conj x).injective, hker₂, Subgroup.map_bot]
    have hcent₂' : cj x A ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
      have hmap : Subgroup.centralizer (L₂ : Set (LGL 2 V)) =
          (Subgroup.centralizer (L₁ : Set (LGL 2 V))).map (MulAut.conj x).toMonoidHom := by
        rw [w183k3m2_centralizer_cj x L₁, hxL]
      rw [hmap]
      exact Subgroup.map_mono hcent₁
    exact w183k3m2r2_alpha_left rows hc htwo hshape hτ hall
      (hc.h131.invariant A hA x hxY) hcard' hker₁' hcent₂'

theorem w183k3m2_false_of_rank_two (rows : Br3Rows)
    (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (htwo : Br3TwoComp Y T L₁ L₂)
    (hshape : IsAlt (↥L₁ ⧸ Subgroup.center ↥L₁) 6 ∨ IsL3 (↥L₁ ⧸ Subgroup.center ↥L₁) 2)
    (hZ : Nat.card ↥(Subgroup.center ↥L₁) = 3)
    (hτ : ∃ τ ∈ T, ActsOnDynkinMod (quasiCentre L₁) L₁ τ)
    (hall : ∀ D ∈ Γ, 2 ≤ mRank D) {A : Subgroup (LGL 2 V)} (hA : A ∈ Γ)
    (hrank : mRank A = 2) : False := by
  have hi : 2 ≤ m - i₀ - 1 := by have := hc.hmi; omega
  have hcard : Nat.card ↥A = 4 :=
    w183k3m2_card_eq_four_of_mRank_eq_two (hc.h131.isElemAb A hA) hrank
  have h4 : 4 ≤ Nat.card ↥A := by rw [hcard]
  have hn := w183k3m2_mem_normalizer hc htwo hall hA
  have hm₁ : mOf A (A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≤ 2 :=
    (w183k3m2_mOf_le_mRank inf_le_left).trans (le_of_eq hrank)
  have hm₂ : mOf A (A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ≤ 2 :=
    (w183k3m2_mOf_le_mRank inf_le_left).trans (le_of_eq hrank)
  have hc₂ : IsCover3 ↥L₂ := htwo.isCover3_swap ⟨htwo.quasi₁, hZ, hshape.symm⟩
  obtain ⟨-, hconfig⟩ := br3_I2_member_free rows hc.h131 hc.vfix hi htwo hshape.symm hc₂.2.2
    hA h4 hn.1 hn.2 hm₁ hm₂
  exact w183k3m2_false_of_alpha_config rows hc htwo hshape hτ hall hA hcard hconfig

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
