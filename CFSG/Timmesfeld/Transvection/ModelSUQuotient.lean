module

public import CFSG.Timmesfeld.Transvection.ModelSURadical
public import CFSG.Timmesfeld.Transvection.ModelRankSU

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed
  CFSG.LieType.BorelTits

namespace ModelRank

section Normalizer

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem uLine_le_normalizer_uRad (a : Fin m → F) :
    uLine σ a ≤ Subgroup.normalizer (uRad σ a : Set (SU σ m)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_uRad hg hx, fun hx => ?_⟩
  have := conj_mem_uRad (inv_mem hg) hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem exists_mem_uLine_of_mem_normalizer_map_of_involutive [CharP F 2]
    (hσ : ∀ c, σ (σ c) = c) (hP : SUPerpStmt σ m) {K : Type*} [Group K] {Φ : SU σ m →* K}
    (hΦ : Function.Surjective Φ) (hker : Φ.ker ≤ Subgroup.center (SU σ m)) {a : Fin m → F}
    (ha : a ≠ 0) (haa : uForm σ a a = 0) {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ a T)
    {k : K} (hk : k ∈ Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)) :
    ∃ g ∈ uLine σ a, Φ g = k := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  obtain ⟨g, rfl⟩ := hΦ k
  set v := suMat σ m g *ᵥ a
  have hv : v ≠ 0 := suMat_mulVec_ne_zero σ g ha
  have hvv : uForm σ v v = 0 := (uForm_mulVec σ g a a).trans haa
  have hTv : IsUTransGroup σ v (conjSub T g) := hT.conjSub g
  have hmap : (conjSub T g).map Φ = T.map Φ := by
    rw [← conjSub_map]
    ext y
    rw [mem_conjSub]
    exact (Subgroup.mem_normalizer_iff''.1 hk y).symm
  by_cases hprop : ∃ μ : F, v = μ • a
  · obtain ⟨μ, hμ⟩ := hprop
    refine ⟨g, ⟨μ, ?_, hμ⟩, rfl⟩
    rintro rfl
    rw [zero_smul] at hμ
    exact hv hμ
  exfalso
  have hprop' : ∀ c : F, v ≠ c • a := fun c hc => hprop ⟨c, hc⟩
  have hc₁ : Commuting ((conjSub T g).map Φ) (T.map Φ) := by
    rw [hmap]
    exact commuting_map Φ (hT.commuting hσ hT haa)
  have hva : uForm σ v a = 0 := by
    rcases hTv.uForm_eq_zero_of_center hσ one_ne_zero h1 hT hv hvv haa
        (commutator_mem_center hker hc₁) with h | ⟨l, hl⟩
    · exact h
    · have hl0 : l ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hl
        exact ha hl
      exact (hprop' l⁻¹ (by rw [hl, smul_smul, inv_mul_cancel₀ hl0, one_smul])).elim
  obtain ⟨z, hzz, haz, hvz⟩ := hP ha haa hvv (uForm_eq_zero_comm hσ hva) hprop'
  have hz : z ≠ 0 := by
    rintro rfl
    exact haz (uForm_zero_right a)
  obtain ⟨Tz, hTz⟩ := exists_isUTransGroup hσ hzz
  have hc₂ : Commuting (Tz.map Φ) (T.map Φ) := by
    rw [← hmap]
    exact commuting_map Φ (hTz.commuting hσ hTv (uForm_eq_zero_comm hσ hvz))
  rcases hTz.uForm_eq_zero_of_center hσ one_ne_zero h1 hT hz hzz haa
      (commutator_mem_center hker hc₂) with h | ⟨l, hl⟩
  · exact haz (uForm_eq_zero_comm hσ h)
  · apply haz
    rw [hl, uForm_smul_left, hzz, mul_zero]

end Normalizer

theorem exists_mem_uLine_of_mem_normalizer_map {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ}
    (hP : SUPerpStmt (unitaryInvolution F 2 f) m) {K : Type} [Group K]
    {Φ : SU (unitaryInvolution F 2 f) m →* K} (hΦ : Function.Surjective Φ)
    (hker : Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m)) {a : Fin m → F}
    (ha : a ≠ 0) (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    {T : Subgroup (SU (unitaryInvolution F 2 f) m)}
    (hT : IsUTransGroup (unitaryInvolution F 2 f) a T)
    {k : K} (hk : k ∈ Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)) :
    ∃ g ∈ uLine (unitaryInvolution F 2 f) a, Φ g = k :=
  exists_mem_uLine_of_mem_normalizer_map_of_involutive (unitaryInvolution_involutive hF) hP hΦ
    hker ha haa hT hk

end ModelRank

end CFSG.Timmesfeld.Transvection
