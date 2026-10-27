module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Conj
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open Matrix
open scoped MatrixGroups

section Quat

variable {K : Type} [Field K]

theorem exists_two_squares [Fintype K] (hK : Fintype.card K % 2 = 1) :
    ∃ a b : K, a ^ 2 + b ^ 2 = -1 := by
  have hf : (Polynomial.X ^ 2 : Polynomial K).degree = 2 := by compute_degree!
  have hg : (Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial K).degree = 2 := by compute_degree!
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hK
  refine ⟨a, b, ?_⟩
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_C] at hab
  linear_combination hab

theorem entries_of_mem_center {x : SL(2, K)} (hx : x ∈ Subgroup.center SL(2, K)) :
    (x : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ (x : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      (x : Matrix (Fin 2) (Fin 2) K) 0 0 = (x : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hx
  have h01 := congrFun (congrFun hr 0) 1
  have h10 := congrFun (congrFun hr 1) 0
  have h00 := congrFun (congrFun hr 0) 0
  have h11 := congrFun (congrFun hr 1) 1
  simp [Matrix.scalar_apply, Matrix.diagonal_apply] at h01 h10 h00 h11
  exact ⟨h01.symm, h10.symm, h00.symm.trans h11⟩

theorem mem_center_of_scalar {x : SL(2, K)} (r : K) (hr : r ^ 2 = 1)
    (hx : (x : Matrix (Fin 2) (Fin 2) K) = r • (1 : Matrix (Fin 2) (Fin 2) K)) :
    x ∈ Subgroup.center SL(2, K) := by
  refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨r, by simpa using hr, ?_⟩
  rw [hx]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

end Quat

section Explicit

variable {K : Type} [Field K]

@[expose] def qI : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

@[expose] def qJ (a b : K) : Matrix (Fin 2) (Fin 2) K := !![a, b; b, -a]

@[expose] def qU (a b h : K) : Matrix (Fin 2) (Fin 2) K :=
  !![h * (a + b - 1), h * (1 + b - a); h * (b - a - 1), h * (-(a + b + 1))]

variable {a b h : K}

theorem det_qI : (qI : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  simp [qI, Matrix.det_fin_two_of]

theorem det_qJ (hab : a ^ 2 + b ^ 2 = -1) : (qJ a b).det = 1 := by
  rw [qJ, Matrix.det_fin_two_of]
  linear_combination (-1 : K) * hab

theorem det_qU (hab : a ^ 2 + b ^ 2 = -1) (hh : 2 * h = 1) : (qU a b h).det = 1 := by
  rw [qU, Matrix.det_fin_two_of]
  linear_combination (-h) * hab + (-a ^ 2 * h - b ^ 2 * h + h + 1) * hh

theorem qI_mul_qI : (qI : Matrix (Fin 2) (Fin 2) K) * qI = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qI, Matrix.mul_apply, Fin.sum_univ_two]

theorem qJ_mul_qJ (hab : a ^ 2 + b ^ 2 = -1) : qJ a b * qJ a b = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qJ, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    first
    | ring1
    | linear_combination hab

theorem qI_mul_qJ : (qI : Matrix (Fin 2) (Fin 2) K) * qJ a b = -(qJ a b * qI) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qI, qJ, Matrix.mul_apply, Fin.sum_univ_two]

theorem qU_mul_qI (hab : a ^ 2 + b ^ 2 = -1) :
    qU a b h * qI = (qI * qJ a b) * qU a b h := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qI, qJ, qU, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    first
    | ring1
    | linear_combination h * hab
    | linear_combination (-h) * hab

theorem qU_mul_qJ (hab : a ^ 2 + b ^ 2 = -1) : qU a b h * qJ a b = qI * qU a b h := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qI, qJ, qU, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    first
    | ring1
    | linear_combination h * hab
    | linear_combination (-h) * hab

theorem qU_sq (hab : a ^ 2 + b ^ 2 = -1) (hh : 2 * h = 1) :
    qU a b h * qU a b h + qU a b h + 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qU, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    first
    | ring1
    | linear_combination h * hab + (a ^ 2 * h + b ^ 2 * h - a * h - b * h - 1) * hh
    | linear_combination (a * h - b * h - h) * hh
    | linear_combination (a * h - b * h + h) * hh
    | linear_combination h * hab + (a ^ 2 * h + b ^ 2 * h + a * h + b * h - 1) * hh

theorem qU_ne_scalar (hh : 2 * h = 1) (c : K) :
    qU a b h ≠ c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  intro hc
  have hh0 : h ≠ 0 := fun h0 => by
    rw [h0] at hh
    simp at hh
  have e1 := congrFun (congrFun hc 0) 1
  have e2 := congrFun (congrFun hc 1) 0
  simp [qU] at e1 e2
  have e1' := e1.resolve_left hh0
  have e2' := e2.resolve_left hh0
  have h2z : (2 : K) = 0 := by linear_combination e1' - e2'
  rw [h2z, zero_mul] at hh
  exact zero_ne_one hh

end Explicit

section Elements

variable {K : Type} [Field K]

theorem inv_mul_mem_center_of_neg {x y : SL(2, K)}
    (hxy : (y : Matrix (Fin 2) (Fin 2) K) = -(x : Matrix (Fin 2) (Fin 2) K)) :
    x⁻¹ * y ∈ Subgroup.center SL(2, K) := by
  refine mem_center_of_scalar (-1) (by norm_num) ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, hxy, Matrix.mul_neg,
    Matrix.adjugate_mul, x.2, one_smul]
  simp

theorem exists_quat (h2 : (2 : K) ≠ 0) {a b : K} (hab : a ^ 2 + b ^ 2 = -1) :
    ∃ I J u : SL(2, K),
      I * I ∈ Subgroup.center SL(2, K) ∧ J * J ∈ Subgroup.center SL(2, K) ∧
      (I * J)⁻¹ * (J * I) ∈ Subgroup.center SL(2, K) ∧
      I ∉ Subgroup.center SL(2, K) ∧ J ∉ Subgroup.center SL(2, K) ∧
      I⁻¹ * J ∉ Subgroup.center SL(2, K) ∧
      u * I * u⁻¹ = I * J ∧ u * J * u⁻¹ = I ∧
      (u : Matrix (Fin 2) (Fin 2) K) * u + u + 1 = 0 ∧
      ∀ c : K, (u : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨h, hh⟩ : ∃ h : K, 2 * h = 1 := ⟨2⁻¹, mul_inv_cancel₀ h2⟩
  obtain ⟨I, hIm⟩ : ∃ I : SL(2, K), (I : Matrix (Fin 2) (Fin 2) K) = qI := ⟨⟨qI, det_qI⟩, rfl⟩
  obtain ⟨J, hJm⟩ : ∃ J : SL(2, K), (J : Matrix (Fin 2) (Fin 2) K) = qJ a b :=
    ⟨⟨qJ a b, det_qJ hab⟩, rfl⟩
  obtain ⟨u, hum⟩ : ∃ u : SL(2, K), (u : Matrix (Fin 2) (Fin 2) K) = qU a b h :=
    ⟨⟨qU a b h, det_qU hab hh⟩, rfl⟩
  have hmul : ∀ x y : SL(2, K), ((x * y : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (x : Matrix (Fin 2) (Fin 2) K) * y := fun x y => Matrix.SpecialLinearGroup.coe_mul x y
  have hIJ : ((I * J : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = qI * qJ a b := by
    rw [hmul, hIm, hJm]
  have hJI : ((J * I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -(qI * qJ a b) := by
    rw [hmul, hIm, hJm, qI_mul_qJ, neg_neg]
  refine ⟨I, J, u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine mem_center_of_scalar (-1) (by norm_num) ?_
    rw [hmul, hIm, qI_mul_qI]
    simp
  · refine mem_center_of_scalar (-1) (by norm_num) ?_
    rw [hmul, hJm, qJ_mul_qJ hab]
    simp
  · exact inv_mul_mem_center_of_neg (by rw [hIJ, hJI])
  · intro hc
    have := (entries_of_mem_center hc).1
    rw [hIm] at this
    simp [qI] at this
  · intro hc
    obtain ⟨e01, -, e00⟩ := entries_of_mem_center hc
    rw [hJm] at e01 e00
    simp [qJ] at e01 e00
    have ha : a = 0 := by
      have : (2 : K) * a = 0 := by linear_combination e00
      exact (mul_eq_zero.1 this).resolve_left h2
    rw [ha, e01] at hab
    simp at hab
  · intro hc
    obtain ⟨e01, -, e00⟩ := entries_of_mem_center hc
    have hm : ((I⁻¹ * J : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![-b, a; a, b] := by
      rw [hmul, Matrix.SpecialLinearGroup.coe_inv, hIm, hJm, qI, qJ, Matrix.adjugate_fin_two_of]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hm] at e01 e00
    simp at e01 e00
    have hb : b = 0 := by
      have : (2 : K) * b = 0 := by linear_combination -e00
      exact (mul_eq_zero.1 this).resolve_left h2
    rw [hb, e01] at hab
    simp at hab
  · have h1 : u * I = (I * J) * u := by
      apply Subtype.ext
      simp only [hmul, hum, hIm, hJm]
      exact qU_mul_qI hab
    exact mul_inv_eq_iff_eq_mul.2 h1
  · have h1 : u * J = I * u := by
      apply Subtype.ext
      simp only [hmul, hum, hIm, hJm]
      exact qU_mul_qJ hab
    exact mul_inv_eq_iff_eq_mul.2 h1
  · rw [hum]
    exact qU_sq hab hh
  · rw [hum]
    exact fun c => qU_ne_scalar hh c

end Elements

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
