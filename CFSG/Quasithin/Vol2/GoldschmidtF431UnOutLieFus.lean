module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentFixed
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Weights

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem fus_coords {a b c d : K} (hb : h.bar b = b)
    (hd : d + h.bar d + a * h.bar c + h.bar a * c = 0)
    (hp2 : miyamotoXGL h a b c d * miyamotoXGL h a b c d = 1) (ha : a ≠ 0) :
    b = 0 ∧ ∃ l : K, h.bar l = l ∧ h.bar d = d ∧
      (miyamotoXGL h 0 l 0 0)⁻¹ * miyamotoXGL h a 0 c d * miyamotoXGL h 0 l 0 0 =
        miyamotoXGL h a 0 0 d ∧
      (miyamotoR2 K)⁻¹ * miyamotoXGL h a 0 0 d * miyamotoR2 K = miyamotoXGL h 0 0 a d := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  rw [miyamotoXGL_mul_self h hb, ← miyamotoXGL_zero h, miyamotoXGL_inj] at hp2
  obtain ⟨-, -, hab, htr⟩ := hp2
  have hb0 : b = 0 := (mul_eq_zero.1 hab).resolve_left ha
  subst hb0
  simp only [mul_zero, zero_add] at htr
  refine ⟨rfl, ?_⟩
  have hba : h.bar a ≠ 0 := by simpa using ha
  set l := c / a with hl
  have hlF : h.bar l = l := by
    rw [hl, map_div₀, div_eq_div_iff hba ha]
    linear_combination -htr + (a * h.bar c) * h2
  have hdF : h.bar d = d := by
    rw [← add_bar_eq_zero_iff h]
    linear_combination hd - htr
  refine ⟨l, hlF, hdF, ?_, ?_⟩
  · rw [miyamotoXGL_conj h hlF (map_zero _), miyamotoXGL_inj]
    refine ⟨rfl, rfl, ?_, by simp⟩
    rw [hl]
    field_simp
    linear_combination c * h2
  · apply Units.ext
    rw [show (miyamotoR2 K)⁻¹ = miyamotoR2 K from inv_eq_of_mul_eq_one_right miyamotoR2_mul_self]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Units.val_mul, miyamotoR2, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four]

end CFSG.Quasithin.H13.F431.Un.OL
