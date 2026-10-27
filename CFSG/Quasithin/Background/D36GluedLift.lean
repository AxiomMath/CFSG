module

public import CFSG.Quasithin.Background.D36GluedOffender

public section

namespace CFSG.Quasithin

section Abstract

variable {Y : Type} [CommGroup Y]

theorem fixed_comm_of_involution (hY : ∀ y : Y, y ^ 2 = 1) {r : MulAut Y} (hr : r * r = 1)
    (z : Y) : r (r z * z⁻¹) = r z * z⁻¹ := by
  have h1 : r (r z) = z := by
    have := congrArg (fun φ : MulAut Y => φ z) hr
    simpa [MulAut.mul_apply] using this
  have h2 : (r z * z⁻¹) ^ 2 = 1 := hY _
  rw [map_mul, map_inv, h1]
  have h3 : (r z * z⁻¹)⁻¹ = r z * z⁻¹ := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h2)
  rw [← h3]
  simp [mul_comm]

theorem exists_fixed_of_commutators (hY : ∀ y : Y, y ^ 2 = 1) {R : Subgroup (MulAut Y)}
    (hR : ∀ r ∈ R, r * r = 1) (hne : ∃ r ∈ R, r ≠ 1) {D U : Subgroup Y} (hD : D ≤ fixV R)
    (hRU : ∀ r ∈ R, ∀ u ∈ U, r u ∈ U) {x : Y}
    (hx : ∀ r ∈ R, r ≠ 1 → ∃ z ∈ U, (r z * z⁻¹) * x⁻¹ ∈ D) :
    ∃ y ∈ U, y * x⁻¹ ∈ D ∧ y ∈ fixV R := by
  obtain ⟨r₀, hr₀, hr₀1⟩ := hne
  obtain ⟨z₀, hz₀, hz₀D⟩ := hx r₀ hr₀ hr₀1
  have hyU : r₀ z₀ * z₀⁻¹ ∈ U := U.mul_mem (hRU r₀ hr₀ z₀ hz₀) (U.inv_mem hz₀)
  refine ⟨r₀ z₀ * z₀⁻¹, hyU, hz₀D, fun ρ hρ => ?_⟩
  by_cases hρ1 : ρ = 1
  · rw [hρ1]; rfl
  obtain ⟨z, hz, hzD⟩ := hx ρ hρ hρ1
  have hd : (r₀ z₀ * z₀⁻¹) * (ρ z * z⁻¹)⁻¹ ∈ D := by
    have := D.mul_mem hz₀D (D.inv_mem hzD)
    have e : (r₀ z₀ * z₀⁻¹) * (ρ z * z⁻¹)⁻¹ =
        ((r₀ z₀ * z₀⁻¹) * x⁻¹) * ((ρ z * z⁻¹) * x⁻¹)⁻¹ := by group
    rw [e]
    exact this
  obtain ⟨d, hd_def⟩ : ∃ d, d = (r₀ z₀ * z₀⁻¹) * (ρ z * z⁻¹)⁻¹ := ⟨_, rfl⟩
  rw [← hd_def] at hd
  have hy : r₀ z₀ * z₀⁻¹ = d * (ρ z * z⁻¹) := by
    rw [hd_def]; exact (inv_mul_cancel_right _ _).symm
  rw [hy, map_mul, hD hd ρ hρ, fixed_comm_of_involution hY (hR ρ hρ) z]

end Abstract

section Glued

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

namespace GluedSwap

theorem false_of_commutators (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1)
    (hL₀X : L₀ ≤ X) (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u)
    (hcom : ∀ x ∈ commModSub U (A ⊓ stabSub U) (U ⊓ U'), ∀ r ∈ glueDiagSub L₀ A U, r ≠ 1 →
      ∃ z ∈ U, (r z * z⁻¹) * x⁻¹ ∈ U ⊓ U') : False := by
  obtain ⟨-, -, -, -, -, hlt⟩ := h.diag_bound hY hL₀X hL₀ hdiag
  have hRU' : ∀ ρ ∈ glueDiagSub L₀ A U, ∀ u ∈ U', ρ u = u := fun ρ hρ u hu =>
    hL₀ ρ (glueDiagSub_le hρ) u hu
  have hDR : U ⊓ U' ≤ fixV (glueDiagSub L₀ A U) := fun d hd ρ hρ => hRU' ρ hρ d hd.2
  have hRU : ∀ r ∈ glueDiagSub L₀ A U, ∀ u ∈ U, r u ∈ U := by
    intro r hr u hu
    obtain ⟨-, b, hb, e⟩ := hr
    rw [← e u hu]
    exact (hb.2 u).mpr hu
  have hne : ∃ r ∈ glueDiagSub L₀ A U, r ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact h.diag_ne_bot hdiag (eq_bot_iff.mpr fun g hg => hcon g hg)
  have hsq : ∀ r ∈ glueDiagSub L₀ A U, r * r = 1 := fun r hr => by
    simpa [pow_two] using h.diag_sq hL₀ hr
  have hle : commModSub U (A ⊓ stabSub U) (U ⊓ U') ≤ U ⊓ fixV (glueDiagSub L₀ A U) := by
    intro x hx
    obtain ⟨y, hyU, hyD, hyfix⟩ := exists_fixed_of_commutators hY hsq hne hDR hRU (hcom x hx)
    refine ⟨hx.1, ?_⟩
    have hxD : x * y⁻¹ ∈ U ⊓ U' := by
      have := (U ⊓ U').inv_mem hyD
      simpa [mul_comm] using this
    intro ρ hρ
    have e : x = (x * y⁻¹) * y := by simp
    rw [e, map_mul, hyfix ρ hρ, hDR hxD ρ hρ]
  have := rk_mono hle
  omega

end GluedSwap

end Glued

end CFSG.Quasithin
