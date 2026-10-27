module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieLocB

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem syl_entries {A : Matrix (Fin 2) (Fin 2) K}
    (hA : A * !![0, 1; 1, 0] * (A.map h.bar)ᵀ = !![0, 1; 1, 0]) :
    A 0 1 * h.bar (A 0 0) + A 0 0 * h.bar (A 0 1) = 0 ∧
    A 0 1 * h.bar (A 1 0) + A 0 0 * h.bar (A 1 1) = 1 ∧
    A 1 1 * h.bar (A 0 0) + A 1 0 * h.bar (A 0 1) = 1 ∧
    A 1 1 * h.bar (A 1 0) + A 1 0 * h.bar (A 1 1) = 0 := by
  have e := fun i j => congrFun (congrFun hA i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  exact ⟨e00, e01, e10, e11⟩

theorem syl_bar_mul_det {A : Matrix (Fin 2) (Fin 2) K}
    (hA : A * !![0, 1; 1, 0] * (A.map h.bar)ᵀ = !![0, 1; 1, 0]) (i j : Fin 2) :
    h.bar (A i j) * A.det = A i j := by
  have hchar : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨e00, e01, e10, e11⟩ := syl_entries hA
  rw [Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one]
  · linear_combination A 0 0 * e10 - A 1 0 * e00
  · linear_combination A 1 1 * e00 - A 0 1 * e10 - A 0 1 * h2
  · linear_combination A 0 0 * e11 - A 1 0 * e01 - A 1 0 * h2
  · linear_combination A 1 1 * e01 - A 0 1 * e11

theorem syl_det_norm {A : Matrix (Fin 2) (Fin 2) K}
    (hA : A * !![0, 1; 1, 0] * (A.map h.bar)ᵀ = !![0, 1; 1, 0]) :
    A.det * h.bar A.det = 1 := by
  have := congrArg Matrix.det hA
  rw [det_mul, det_mul, det_conjTranspose', Matrix.det_fin_two_of] at this
  have h' : A.det * h.bar A.det * (-1) = -1 := by linear_combination this
  linear_combination -h'

theorem syl_eq_one_of_mul_self [CharP K 2] {x : K} (hx : x * x = 1) : x = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : (x - 1) * (x - 1) = 0 := by linear_combination hx + (1 - x) * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp this)

theorem syl_scalar_decomp {A : Matrix (Fin 2) (Fin 2) K}
    (hA : A * !![0, 1; 1, 0] * (A.map h.bar)ᵀ = !![0, 1; 1, 0]) :
    ∃ (lam : K) (B : SpecialLinearGroup (Fin 2) h.fixedField),
      lam * h.bar lam = 1 ∧ A = lam • slM B := by
  have hchar : CharP K 2 := h.charP
  have hfin : Finite K := h.finite
  obtain ⟨lam, hlam⟩ := isSquare_of_charTwo' A.det
  have hnorm := syl_det_norm hA
  have hl1 : lam * h.bar lam = 1 := by
    apply syl_eq_one_of_mul_self
    rw [hlam, map_mul] at hnorm
    linear_combination hnorm
  have hl0 : lam ≠ 0 := left_ne_zero_of_mul_eq_one hl1
  have hfix : ∀ i j, h.bar (lam⁻¹ * A i j) = lam⁻¹ * A i j := by
    intro i j
    have e := syl_bar_mul_det hA i j
    have hb : h.bar lam = lam⁻¹ := eq_inv_of_mul_eq_one_right hl1
    have hdl : A.det ≠ 0 := by rw [hlam]; exact mul_ne_zero hl0 hl0
    rw [map_mul, map_inv₀, hb, inv_inv]
    have e' : h.bar (A i j) = A i j / A.det := by
      rw [eq_div_iff hdl]; exact e
    rw [e', hlam]
    field_simp
  have hdet1 : (lam⁻¹ • A).det = 1 := by
    rw [Matrix.det_smul, hlam]
    simp only [Fintype.card_fin]
    field_simp
  let B : SpecialLinearGroup (Fin 2) h.fixedField :=
    ⟨Matrix.of fun i j => (⟨lam⁻¹ * A i j, hfix i j⟩ : h.fixedField), by
      apply Subtype.ext
      have := hdet1
      rw [Matrix.det_fin_two] at this ⊢
      simpa using this⟩
  refine ⟨lam, B, hl1, ?_⟩
  ext i j
  rw [Matrix.smul_apply, slM_apply, smul_eq_mul]
  show A i j = lam * (lam⁻¹ * A i j)
  rw [← mul_assoc, mul_inv_cancel₀ hl0, one_mul]

end CFSG.Quasithin.H13.F431.Un.L5
