module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.H13.F431.F45

namespace Sl2

variable {F : Type} [Field F]

theorem exists_scalar {s t s' t' : F} (hd : s ≠ 0 ∨ t ≠ 0) (hd' : s' ≠ 0 ∨ t' ≠ 0)
    (h0 : s * t' - t * s' = 0) : ∃ l : F, l ≠ 0 ∧ s = l * s' ∧ t = l * t' := by
  by_cases hs' : s' = 0
  · have ht' : t' ≠ 0 := hd'.resolve_left (not_not.mpr hs')
    subst hs'
    have hs : s = 0 := by
      have : s * t' = 0 := by linear_combination h0
      exact (mul_eq_zero.mp this).resolve_right ht'
    refine ⟨t / t', ?_, by simp [hs], by field_simp⟩
    intro hl
    rw [div_eq_zero_iff] at hl
    rcases hl with hl | hl
    · rcases hd with hd | hd
      · exact hd hs
      · exact hd hl
    · exact ht' hl
  · refine ⟨s / s', ?_, by field_simp, ?_⟩
    · intro hl
      rw [div_eq_zero_iff] at hl
      rcases hl with hl | hl
      · have ht : t = 0 := by
          have : t * s' = 0 := by linear_combination -h0 + t' * hl
          exact (mul_eq_zero.mp this).resolve_right hs'
        rcases hd with hd | hd
        · exact hd hl
        · exact hd ht
      · exact hs' hl
    · field_simp
      linear_combination -h0

theorem sl2_two_trans (w₁ w₂ w₁' w₂' z₁ z₂ z₁' z₂' : F) (hΔ : w₁ * w₂' - w₂ * w₁' ≠ 0)
    (hΔz : z₁ * z₂' - z₂ * z₁' ≠ 0) :
    ∃ (N : Matrix.SpecialLinearGroup (Fin 2) F) (κ : F), κ ≠ 0 ∧
      N 0 0 * w₁ + N 0 1 * w₂ = z₁ ∧ N 1 0 * w₁ + N 1 1 * w₂ = z₂ ∧
      N 0 0 * w₁' + N 0 1 * w₂' = κ * z₁' ∧ N 1 0 * w₁' + N 1 1 * w₂' = κ * z₂' := by
  obtain ⟨Δ, hΔd⟩ : ∃ Δ : F, Δ = w₁ * w₂' - w₂ * w₁' := ⟨_, rfl⟩
  obtain ⟨Δz, hΔzd⟩ : ∃ Δz : F, Δz = z₁ * z₂' - z₂ * z₁' := ⟨_, rfl⟩
  have hΔ' : Δ ≠ 0 := hΔd ▸ hΔ
  have hΔz' : Δz ≠ 0 := hΔzd ▸ hΔz
  obtain ⟨κ, hκ⟩ : ∃ κ : F, κ = Δ / Δz := ⟨_, rfl⟩
  have hκ0 : κ ≠ 0 := by rw [hκ]; exact div_ne_zero hΔ' hΔz'
  have hdet : ((z₁ * w₂' - κ * z₁' * w₂) / Δ) * ((κ * z₂' * w₁ - z₂ * w₁') / Δ) -
      ((κ * z₁' * w₁ - z₁ * w₁') / Δ) * ((z₂ * w₂' - κ * z₂' * w₂) / Δ) = 1 := by
    rw [hκ]
    field_simp
    subst hΔd hΔzd
    ring
  refine ⟨⟨!![(z₁ * w₂' - κ * z₁' * w₂) / Δ, (κ * z₁' * w₁ - z₁ * w₁') / Δ;
      (z₂ * w₂' - κ * z₂' * w₂) / Δ, (κ * z₂' * w₁ - z₂ * w₁') / Δ], by
        rw [Matrix.det_fin_two_of]
        exact hdet⟩, κ, hκ0, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    subst hΔd
    ring

end Sl2

end CFSG.Quasithin.H13.F431.F45
