module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open Matrix

variable {F : Type} [Field F]

abbrev cnj (A M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F := A * M * adjugate A

theorem trace_cnj (A M : Matrix (Fin 3) (Fin 3) F) : (cnj A M).trace = A.det * M.trace := by
  rw [cnj, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]

section Entries

variable {A M : Matrix (Fin 3) (Fin 3) F} (h10 : A 1 0 = 0) (h20 : A 2 0 = 0)
include h10 h20

theorem det_of_par : A.det = A 0 0 * (A 1 1 * A 2 2 - A 1 2 * A 2 1) := by
  rw [Matrix.det_fin_three, h10, h20]
  ring

theorem cnj_col0 (i : Fin 3) (hi : i ≠ 0) :
    cnj A M i 0 = (A 1 1 * A 2 2 - A 1 2 * A 2 1) * (A i 1 * M 1 0 + A i 2 * M 2 0) := by
  have hi0 : A i 0 = 0 := by fin_cases i <;> simp_all
  simp only [cnj, Matrix.mul_apply, Fin.sum_univ_three, adjugate_fin_three, of_apply,
    cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val', cons_val_fin_one,
    head_fin_const, tail_cons, h10, h20, hi0]
  ring

theorem cnj_00 (hM10 : M 1 0 = 0) (hM20 : M 2 0 = 0) :
    cnj A M 0 0 = A 0 0 * M 0 0 * (A 1 1 * A 2 2 - A 1 2 * A 2 1) := by
  simp only [cnj, Matrix.mul_apply, Fin.sum_univ_three, adjugate_fin_three, of_apply,
    cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val', cons_val_fin_one,
    head_fin_const, tail_cons, h10, h20, hM10, hM20]
  ring

omit h10 h20 in
theorem cnj_row0_of_Wp (hM : ∀ i j : Fin 3, ¬ (i = 0 ∧ j ≠ 0) → M i j = 0) (j : Fin 3) :
    cnj A M 0 j = A 0 0 * (M 0 1 * adjugate A 1 j + M 0 2 * adjugate A 2 j) := by
  have h00 := hM 0 0 (by simp)
  have h1 : ∀ k, M 1 k = 0 := fun k => hM 1 k (by simp)
  have h2 : ∀ k, M 2 k = 0 := fun k => hM 2 k (by simp)
  simp only [cnj, Matrix.mul_apply, Fin.sum_univ_three, h00, h1, h2]
  ring

theorem cnj_block_of_Wp (hM : ∀ i j : Fin 3, ¬ (i = 0 ∧ j ≠ 0) → M i j = 0) (i j : Fin 3)
    (hi : i ≠ 0) : cnj A M i j = 0 := by
  have hi0 : A i 0 = 0 := by fin_cases i <;> simp_all
  have h1 : ∀ k, M 1 k = 0 := fun k => hM 1 k (by simp)
  have h2 : ∀ k, M 2 k = 0 := fun k => hM 2 k (by simp)
  simp only [cnj, Matrix.mul_apply, Fin.sum_univ_three, h1, h2, hi0]
  ring

theorem cnj_block_of_W2 (hdet : A.det = 1) (hM10 : M 1 0 = 0) (hM20 : M 2 0 = 0)
    (hM12 : M 1 2 = 0) (hM21 : M 2 1 = 0) (hM : M 1 1 = M 2 2) (i j : Fin 3) (hi : i ≠ 0) :
    cnj A M i j = if i = j then M 1 1 else 0 := by
  have hi0 : A i 0 = 0 := by fin_cases i <;> simp_all
  have hadj := congrFun (congrFun (Matrix.mul_adjugate A) i) j
  rw [hdet, one_smul, Matrix.mul_apply, Fin.sum_univ_three, hi0, zero_mul, zero_add] at hadj
  have e : cnj A M i j = M 1 1 * (A i 1 * adjugate A 1 j + A i 2 * adjugate A 2 j) := by
    simp only [cnj, Matrix.mul_apply, Fin.sum_univ_three, hi0, hM10, hM20, hM12, hM21, ← hM]
    ring
  rw [e, hadj, Matrix.one_apply]
  split_ifs <;> simp

theorem cnj_12_of_W3 [CharP F 2] (hM10 : M 1 0 = 0) (hM20 : M 2 0 = 0) (hM : M 1 1 = M 2 2) :
    cnj A M 1 2 = A 0 0 * (A 1 1 ^ 2 * M 1 2 + A 1 2 ^ 2 * M 2 1) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [cnj, Matrix.mul_apply, Fin.sum_univ_three, adjugate_fin_three, of_apply,
    cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val', cons_val_fin_one,
    head_cons, head_fin_const, tail_cons, h10, h20, hM10, hM20, ← hM]
  linear_combination (-(A 0 0 * A 1 2 ^ 2 * M 2 1)) * h2

theorem cnj_21_of_W3 [CharP F 2] (hM10 : M 1 0 = 0) (hM20 : M 2 0 = 0) (hM : M 1 1 = M 2 2) :
    cnj A M 2 1 = A 0 0 * (A 2 1 ^ 2 * M 1 2 + A 2 2 ^ 2 * M 2 1) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [cnj, Matrix.mul_apply, Fin.sum_univ_three, adjugate_fin_three, of_apply,
    cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val', cons_val_fin_one,
    head_fin_const, tail_cons, h10, h20, hM10, hM20, ← hM]
  linear_combination (-(A 0 0 * A 2 1 ^ 2 * M 1 2)) * h2

end Entries

omit [Field F] in
abbrev kp {R : Type} (M : Matrix (Fin 3) (Fin 3) R) : Fin 2 → R := ![M 0 1, M 0 2]

omit [Field F] in
abbrev km {R : Type} (M : Matrix (Fin 3) (Fin 3) R) : Fin 2 → R := ![M 2 0, M 1 0]

abbrev k2 (M : Matrix (Fin 3) (Fin 3) F) : Fin 2 → F := ![M 2 1 ^ 2, M 1 2 ^ 2]

abbrev rhoA (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun i k => A 0 0 * adjugate A k.succ i.succ

section Coords

variable {A M : Matrix (Fin 3) (Fin 3) F} (h10 : A 1 0 = 0) (h20 : A 2 0 = 0)
include h10 h20

omit h10 h20 in
theorem kp_cnj (hM : ∀ i j : Fin 3, ¬ (i = 0 ∧ j ≠ 0) → M i j = 0) :
    kp (cnj A M) = rhoA A *ᵥ kp M := by
  funext i
  fin_cases i <;>
  · simp only [kp, rhoA, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, cnj_row0_of_Wp hM, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.of_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring

theorem km_cnj [CharP F 2] (hδ : A 1 1 * A 2 2 - A 1 2 * A 2 1 = A 0 0 ^ 2) :
    km (cnj A M) = rhoA A *ᵥ km M := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  funext i
  fin_cases i
  · simp only [km, rhoA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      cnj_col0 h10 h20 2 (by decide), Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_one,
      adjugate_fin_three, cons_val', cons_val_two, empty_val',
      cons_val_fin_one, head_fin_const, tail_cons, h10, h20, hδ]
    linear_combination (A 0 0 ^ 2 * A 2 1 * M 1 0) * h2
  · simp only [km, rhoA, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons,
      cnj_col0 h10 h20 1 (by decide), Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero,
      adjugate_fin_three, cons_val', cons_val_two, empty_val', cons_val_fin_one,
      head_fin_const, tail_cons, h10, h20, hδ]
    linear_combination (A 0 0 ^ 2 * A 1 2 * M 2 0) * h2

theorem k2_cnj [CharP F 2] (h4 : ∀ x : F, x ^ 4 = x) (hM10 : M 1 0 = 0) (hM20 : M 2 0 = 0)
    (hM : M 1 1 = M 2 2) : k2 (cnj A M) = rhoA A *ᵥ k2 M := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  funext i
  fin_cases i
  · simp only [k2, rhoA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      cnj_21_of_W3 h10 h20 hM10 hM20 hM, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_one,
      adjugate_fin_three, cons_val', cons_val_two, empty_val',
      cons_val_fin_one, head_fin_const, tail_cons, h10, h20]
    linear_combination A 0 0 ^ 2 * M 1 2 ^ 2 * h4 (A 2 1) + A 0 0 ^ 2 * M 2 1 ^ 2 * h4 (A 2 2) +
      (A 0 0 ^ 2 * A 2 1 ^ 2 * M 1 2 * A 2 2 ^ 2 * M 2 1 + A 0 0 ^ 2 * A 2 1 * M 1 2 ^ 2) * h2
  · simp only [k2, rhoA, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons,
      cnj_12_of_W3 h10 h20 hM10 hM20 hM, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero,
      adjugate_fin_three, cons_val', cons_val_two, empty_val', cons_val_fin_one,
      head_fin_const, tail_cons, h10, h20]
    linear_combination A 0 0 ^ 2 * M 1 2 ^ 2 * h4 (A 1 1) + A 0 0 ^ 2 * M 2 1 ^ 2 * h4 (A 1 2) +
      (A 0 0 ^ 2 * A 1 1 ^ 2 * M 1 2 * A 1 2 ^ 2 * M 2 1 + A 0 0 ^ 2 * A 1 2 * M 2 1 ^ 2) * h2

end Coords

end CFSG.Quasithin.H13.Ch4.B414.M
