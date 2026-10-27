module

public import CFSG.Timmesfeld.LieEmbed.UnitaryWittN

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.LieEmbed

namespace ModelRank

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ}

omit [CharP F 2] in
theorem eq_zero_of_forall_uForm_eq_zero {x : Fin m → F} (h : ∀ u, uForm σ x u = 0) : x = 0 := by
  by_contra hx
  obtain ⟨i, hi⟩ := exists_uForm_single_ne_zero (σ := σ) hx
  exact hi (h _)

omit [CharP F 2] in
theorem exists_uForm_eq_one {a : Fin m → F} (ha : a ≠ 0) : ∃ y, uForm σ a y = 1 := by
  obtain ⟨i, hi⟩ := exists_uForm_single_ne_zero (σ := σ) ha
  exact ⟨(uForm σ a (Pi.single (Fin.rev i) 1))⁻¹ • Pi.single (Fin.rev i) 1,
    by rw [uForm_smul_right, inv_mul_cancel₀ hi]⟩

omit [CharP F 2] in
theorem exists_eq_smul_of_uForm_imp (hσ : ∀ c, σ (σ c) = c) {v w : Fin m → F}
    (h : ∀ u, uForm σ v u = 0 → uForm σ w u = 0) : ∃ l : F, w = l • v := by
  by_cases hv : v = 0
  · refine ⟨0, ?_⟩
    rw [zero_smul]
    exact eq_zero_of_forall_uForm_eq_zero fun u => h u (by simp [hv, uForm_eq])
  obtain ⟨y, hy⟩ := exists_uForm_eq_one (σ := σ) hv
  have hwu : ∀ u, uForm σ w u = uForm σ w y * uForm σ v u := by
    intro u
    have h1 : uForm σ v (u - uForm σ v u • y) = 0 := by
      rw [uForm_sub_right, uForm_smul_right, hy, mul_one, sub_self]
    have h2 := h _ h1
    rw [uForm_sub_right, uForm_smul_right] at h2
    linear_combination h2
  refine ⟨σ (uForm σ w y), ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_uForm_eq_zero (σ := σ) fun u => ?_
  rw [sub_eq_add_neg, ← neg_smul, uForm_add_left, uForm_smul_left, map_neg, hσ, hwu u]
  ring

omit [CharP F 2] in
theorem exists_isotropic_partner (hσ : ∀ c, σ (σ c) = c) (htr : ∀ a, σ a = a → ∃ c, c + σ c = a)
    {a : Fin m → F} (ha : a ≠ 0) (haa : uForm σ a a = 0) :
    ∃ d, uForm σ d d = 0 ∧ uForm σ a d = 1 := by
  obtain ⟨d₀, had₀⟩ := exists_uForm_eq_one (σ := σ) ha
  have hd₀a : uForm σ d₀ a = 1 := by rw [← uForm_conj σ hσ, had₀, map_one]
  obtain ⟨c, hc⟩ := htr (-uForm σ d₀ d₀) (by rw [map_neg, uForm_conj σ hσ])
  refine ⟨d₀ + c • a, ?_, ?_⟩
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, haa, had₀,
      hd₀a]
    linear_combination hc
  · rw [uForm_add_right, uForm_smul_right, haa, mul_zero, add_zero, had₀]

theorem exists_isotropic_both (hσ : ∀ c, σ (σ c) = c) (htr : ∀ a, σ a = a → ∃ c, c + σ c = a)
    {a u : Fin m → F} (ha : a ≠ 0) (hu : u ≠ 0) (haa : uForm σ a a = 0) (huu : uForm σ u u = 0) :
    ∃ y, uForm σ y y = 0 ∧ uForm σ a y ≠ 0 ∧ uForm σ u y ≠ 0 := by
  obtain ⟨d, hdd, had⟩ := exists_isotropic_partner hσ htr ha haa
  by_cases hud : uForm σ u d = 0
  swap
  · exact ⟨d, hdd, by rw [had]; exact one_ne_zero, hud⟩
  obtain ⟨e, hee, hue⟩ := exists_isotropic_partner hσ htr hu huu
  by_cases hae : uForm σ a e = 0
  swap
  · exact ⟨e, hee, hae, by rw [hue]; exact one_ne_zero⟩
  have hed : uForm σ e d = σ (uForm σ d e) := (uForm_conj σ hσ d e).symm
  obtain ⟨t, ht0, ht⟩ : ∃ t : F, t ≠ 0 ∧ σ t * σ (uForm σ d e) + t * uForm σ d e = 0 := by
    by_cases hde : uForm σ d e = 0
    · exact ⟨1, one_ne_zero, by rw [hde, map_zero, mul_zero, mul_zero, add_zero]⟩
    · refine ⟨(uForm σ d e)⁻¹, inv_ne_zero hde, ?_⟩
      rw [← map_mul, inv_mul_cancel₀ hde, map_one]
      exact CharTwo.add_self_eq_zero 1
  refine ⟨d + t • e, ?_, ?_, ?_⟩
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hdd, hee, hed]
    linear_combination ht
  · rw [uForm_add_right, uForm_smul_right, had, hae, mul_zero, add_zero]
    exact one_ne_zero
  · rw [uForm_add_right, uForm_smul_right, hud, hue, mul_one, zero_add]
    exact ht0

omit [CharP F 2] in
theorem exists_isotropic_perp_not_perp (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {a v : Fin m → F} (ha : a ≠ 0)
    (haa : uForm σ a a = 0) (hvv : uForm σ v v = 0) (hav : uForm σ a v = 0)
    (hva : ∀ c : F, v ≠ c • a) : ∃ z, uForm σ z z = 0 ∧ uForm σ a z ≠ 0 ∧ uForm σ v z = 0 := by
  obtain ⟨z₀, hvz₀, haz₀⟩ : ∃ z₀, uForm σ v z₀ = 0 ∧ uForm σ a z₀ ≠ 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨l, hl⟩ := exists_eq_smul_of_uForm_imp hσ hne
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact ha (by rw [hl, zero_smul])
    exact hva l⁻¹ (by rw [hl, smul_smul, inv_mul_cancel₀ hl0, one_smul])
  have hz₀a : uForm σ z₀ a = σ (uForm σ a z₀) := (uForm_conj σ hσ a z₀).symm
  have hσ0 : σ (uForm σ a z₀) ≠ 0 := (map_ne_zero σ).2 haz₀
  obtain ⟨c, hc⟩ := htr (-uForm σ z₀ z₀) (by rw [map_neg, uForm_conj σ hσ])
  have h1 : c * (σ (uForm σ a z₀))⁻¹ * σ (uForm σ a z₀) = c := by
    rw [mul_assoc, inv_mul_cancel₀ hσ0, mul_one]
  have h2 : σ (c * (σ (uForm σ a z₀))⁻¹) * uForm σ a z₀ = σ c := by
    rw [map_mul, map_inv₀, hσ, mul_assoc, inv_mul_cancel₀ haz₀, mul_one]
  refine ⟨z₀ + (c * (σ (uForm σ a z₀))⁻¹) • a, ?_, ?_, ?_⟩
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, haa, hz₀a]
    linear_combination h1 + h2 + hc
  · rw [uForm_add_right, uForm_smul_right, haa, mul_zero, add_zero]
    exact haz₀
  · rw [uForm_add_right, uForm_smul_right, hvz₀, uForm_eq_zero_comm hσ hav, mul_zero, add_zero]

end ModelRank

end CFSG.Timmesfeld.Transvection
