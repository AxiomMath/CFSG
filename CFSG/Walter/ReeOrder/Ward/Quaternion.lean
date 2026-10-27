module

public import CFSG.CharacterTheory.PSL2Table.Basic
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.Walter.Ward.Quaternion

open Matrix CFSG.PSL2Table
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def qi : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

@[expose] def qj (a b : F) (h : a ^ 2 + b ^ 2 = -1) : SL(2, F) :=
  ⟨!![a, b; b, -a], by rw [Matrix.det_fin_two_of]; linear_combination -h⟩

@[expose] def qw (a b : F) (h2 : (2 : F) ≠ 0) (h : a ^ 2 + b ^ 2 = -1) : SL(2, F) :=
  ⟨!![-(1 + a + b) / 2, -(1 + b - a) / 2; -(-1 + b - a) / 2, -(1 - a - b) / 2], by
    rw [Matrix.det_fin_two_of]
    field_simp
    linear_combination (-2 : F) * h⟩

variable {a b : F} (h2 : (2 : F) ≠ 0) (h : a ^ 2 + b ^ 2 = -1)

theorem coe_qi : ((qi : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem coe_qj : ((qj a b h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![a, b; b, -a] := rfl

theorem coe_qw : ((qw a b h2 h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    !![-(1 + a + b) / 2, -(1 + b - a) / 2; -(-1 + b - a) / 2, -(1 - a - b) / 2] := rfl

theorem qi_mul_qi : (qi : SL(2, F)) * qi = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_qi, Matrix.mul_apply, Fin.sum_univ_two]

theorem qj_mul_qj : qj a b h * qj a b h = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_qj, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | ring1 | linear_combination h

theorem qj_mul_qi : qj a b h * qi = -(qi * qj a b h) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_qi, coe_qj, Matrix.mul_apply, Fin.sum_univ_two]

theorem qw_mul_qi : qw a b h2 h * qi = qj a b h * qw a b h2 h := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_qi, coe_qj, coe_qw, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals first | ring1 | linear_combination h | linear_combination -h

theorem qw_mul_qj : qw a b h2 h * qj a b h = (qi * qj a b h) * qw a b h2 h := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_qi, coe_qj, coe_qw, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals ring1

theorem qw_sq : ((qw a b h2 h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * qw a b h2 h =
    -((qw a b h2 h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_qw, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals first | ring1 | linear_combination h | linear_combination -h |
    linear_combination 2 * h

theorem qw_cube : qw a b h2 h ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_three, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← mul_assoc, qw_sq, Matrix.SpecialLinearGroup.coe_one]
  set W := ((qw a b h2 h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
  have hW := qw_sq h2 h
  calc (-W - 1) * W = -(W * W) - W := by noncomm_ring
    _ = 1 := by rw [hW]; abel

theorem qw_ne_one : qw a b h2 h ≠ 1 := by
  intro h1
  have e1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
  have e2 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 0) h1
  simp [coe_qw] at e1 e2
  rcases e1 with e1 | e1
  · rcases e2 with e2 | e2
    · exact h2 (by linear_combination e2 - e1)
    · exact h2 e2
  · exact h2 e1

theorem qw_ne_neg_one : qw a b h2 h ≠ -1 := by
  intro h1
  have e1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
  have e2 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 0) h1
  simp [coe_qw] at e1 e2
  rcases e1 with e1 | e1
  · rcases e2 with e2 | e2
    · exact h2 (by linear_combination e2 - e1)
    · exact h2 e2
  · exact h2 e1

theorem qi_ne_one : (qi : SL(2, F)) ≠ 1 := by
  intro h1
  have e1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
  simp [coe_qi] at e1

theorem qi_ne_neg_one : (qi : SL(2, F)) ≠ -1 := by
  intro h1
  have e1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
  simp [coe_qi] at e1

include h2 in
theorem qj_ne_one : qj a b h ≠ 1 := by
  intro h1
  have e0 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h1
  have e3 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 1) h1
  simp [coe_qj] at e0 e3
  apply h2
  linear_combination -e0 - e3

include h2 in
theorem qj_ne_neg_one : qj a b h ≠ -1 := by
  intro h1
  have e0 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h1
  have e3 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 1) h1
  simp [coe_qj] at e0 e3
  apply h2
  linear_combination e0 - e3

include h2 in
theorem qj_ne_qi : qj a b h ≠ qi := by
  intro h1
  have e1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
  have e2 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 0) h1
  simp [coe_qj, coe_qi] at e1 e2
  apply h2
  linear_combination e2 - e1

include h2 in
theorem qj_ne_neg_qi : qj a b h ≠ -qi := by
  intro h1
  have e1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
  have e2 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 0) h1
  simp [coe_qj, coe_qi] at e1 e2
  apply h2
  linear_combination e1 - e2

omit h2 h in
theorem exists_quaternion [Fintype F] (hF : ringChar F ≠ 2) :
    ∃ v₁ v₂ c : PSL(2, F), v₁ * v₁ = 1 ∧ v₂ * v₂ = 1 ∧ v₁ * v₂ = v₂ * v₁ ∧ v₁ ≠ 1 ∧
      v₂ ≠ 1 ∧ v₁ ≠ v₂ ∧ orderOf c = 3 ∧ c * v₁ * c⁻¹ = v₂ ∧ c * v₂ * c⁻¹ = v₁ * v₂ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨a, b, hab⟩ := exists_normForm_eq hF (ν := -1) (by norm_num) (-1)
  have h : a ^ 2 + b ^ 2 = -1 := by linear_combination hab
  refine ⟨mk qi, mk (qj a b h), mk (qw a b h2 h), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, qi_mul_qi, mk_neg, map_one]
  · rw [← map_mul, qj_mul_qj, mk_neg, map_one]
  · rw [← map_mul, ← map_mul, qj_mul_qi, mk_neg]
  · rw [Ne, mk_eq_one_iff]
    push Not
    exact ⟨qi_ne_one, qi_ne_neg_one⟩
  · rw [Ne, mk_eq_one_iff]
    push Not
    exact ⟨qj_ne_one h2 h, qj_ne_neg_one h2 h⟩
  · rw [Ne, mk_eq_mk_iff]
    push Not
    exact ⟨qj_ne_qi h2 h, qj_ne_neg_qi h2 h⟩
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, qw_cube, map_one]
    · rw [Ne, mk_eq_one_iff]
      push Not
      exact ⟨qw_ne_one h2 h, qw_ne_neg_one h2 h⟩
  · rw [← map_inv, ← map_mul, ← map_mul, qw_mul_qi, mul_inv_cancel_right]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, qw_mul_qj, mul_inv_cancel_right]

end CFSG.Walter.Ward.Quaternion
