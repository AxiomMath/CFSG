module

public import CFSG.LieType.Universal.Spin.Action
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType.RCKFlag

open Matrix

variable {K : Type} [Field K]

abbrev rckSP4_C1 : Matrix (Fin 4) (Fin 4) K :=
  !![1, 1, 0, 0; 0, 1, 0, 0; 0, 1, 1, 0; 1, 1, 1, 1]

abbrev rckSP4_C2 : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 1, 1, 0, 0; 1, 1, 1, 1; 1, 0, 0, 1]

abbrev rckSP4_C3 : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 1; 1, 1, 1, 1; 0, 0, 1, 1; 0, 0, 0, 1]

@[simp] lemma rckSP4_C1_00 : rckSP4_C1 0 0 = (1 : K) := rfl
@[simp] lemma rckSP4_C1_01 : rckSP4_C1 0 1 = (1 : K) := rfl
@[simp] lemma rckSP4_C1_02 : rckSP4_C1 0 2 = (0 : K) := rfl
@[simp] lemma rckSP4_C1_03 : rckSP4_C1 0 3 = (0 : K) := rfl
@[simp] lemma rckSP4_C1_10 : rckSP4_C1 1 0 = (0 : K) := rfl
@[simp] lemma rckSP4_C1_11 : rckSP4_C1 1 1 = (1 : K) := rfl
@[simp] lemma rckSP4_C1_12 : rckSP4_C1 1 2 = (0 : K) := rfl
@[simp] lemma rckSP4_C1_13 : rckSP4_C1 1 3 = (0 : K) := rfl
@[simp] lemma rckSP4_C1_20 : rckSP4_C1 2 0 = (0 : K) := rfl
@[simp] lemma rckSP4_C1_21 : rckSP4_C1 2 1 = (1 : K) := rfl
@[simp] lemma rckSP4_C1_22 : rckSP4_C1 2 2 = (1 : K) := rfl
@[simp] lemma rckSP4_C1_23 : rckSP4_C1 2 3 = (0 : K) := rfl
@[simp] lemma rckSP4_C1_30 : rckSP4_C1 3 0 = (1 : K) := rfl
@[simp] lemma rckSP4_C1_31 : rckSP4_C1 3 1 = (1 : K) := rfl
@[simp] lemma rckSP4_C1_32 : rckSP4_C1 3 2 = (1 : K) := rfl
@[simp] lemma rckSP4_C1_33 : rckSP4_C1 3 3 = (1 : K) := rfl
@[simp] lemma rckSP4_C2_00 : rckSP4_C2 0 0 = (1 : K) := rfl
@[simp] lemma rckSP4_C2_01 : rckSP4_C2 0 1 = (0 : K) := rfl
@[simp] lemma rckSP4_C2_02 : rckSP4_C2 0 2 = (0 : K) := rfl
@[simp] lemma rckSP4_C2_03 : rckSP4_C2 0 3 = (0 : K) := rfl
@[simp] lemma rckSP4_C2_10 : rckSP4_C2 1 0 = (1 : K) := rfl
@[simp] lemma rckSP4_C2_11 : rckSP4_C2 1 1 = (1 : K) := rfl
@[simp] lemma rckSP4_C2_12 : rckSP4_C2 1 2 = (0 : K) := rfl
@[simp] lemma rckSP4_C2_13 : rckSP4_C2 1 3 = (0 : K) := rfl
@[simp] lemma rckSP4_C2_20 : rckSP4_C2 2 0 = (1 : K) := rfl
@[simp] lemma rckSP4_C2_21 : rckSP4_C2 2 1 = (1 : K) := rfl
@[simp] lemma rckSP4_C2_22 : rckSP4_C2 2 2 = (1 : K) := rfl
@[simp] lemma rckSP4_C2_23 : rckSP4_C2 2 3 = (1 : K) := rfl
@[simp] lemma rckSP4_C2_30 : rckSP4_C2 3 0 = (1 : K) := rfl
@[simp] lemma rckSP4_C2_31 : rckSP4_C2 3 1 = (0 : K) := rfl
@[simp] lemma rckSP4_C2_32 : rckSP4_C2 3 2 = (0 : K) := rfl
@[simp] lemma rckSP4_C2_33 : rckSP4_C2 3 3 = (1 : K) := rfl
@[simp] lemma rckSP4_C3_00 : rckSP4_C3 0 0 = (1 : K) := rfl
@[simp] lemma rckSP4_C3_01 : rckSP4_C3 0 1 = (0 : K) := rfl
@[simp] lemma rckSP4_C3_02 : rckSP4_C3 0 2 = (0 : K) := rfl
@[simp] lemma rckSP4_C3_03 : rckSP4_C3 0 3 = (1 : K) := rfl
@[simp] lemma rckSP4_C3_10 : rckSP4_C3 1 0 = (1 : K) := rfl
@[simp] lemma rckSP4_C3_11 : rckSP4_C3 1 1 = (1 : K) := rfl
@[simp] lemma rckSP4_C3_12 : rckSP4_C3 1 2 = (1 : K) := rfl
@[simp] lemma rckSP4_C3_13 : rckSP4_C3 1 3 = (1 : K) := rfl
@[simp] lemma rckSP4_C3_20 : rckSP4_C3 2 0 = (0 : K) := rfl
@[simp] lemma rckSP4_C3_21 : rckSP4_C3 2 1 = (0 : K) := rfl
@[simp] lemma rckSP4_C3_22 : rckSP4_C3 2 2 = (1 : K) := rfl
@[simp] lemma rckSP4_C3_23 : rckSP4_C3 2 3 = (1 : K) := rfl
@[simp] lemma rckSP4_C3_30 : rckSP4_C3 3 0 = (0 : K) := rfl
@[simp] lemma rckSP4_C3_31 : rckSP4_C3 3 1 = (0 : K) := rfl
@[simp] lemma rckSP4_C3_32 : rckSP4_C3 3 2 = (0 : K) := rfl
@[simp] lemma rckSP4_C3_33 : rckSP4_C3 3 3 = (1 : K) := rfl

theorem rckSP4_matrix4_eq_one (h2 : (2 : K) = 0)
    (M : Matrix (Fin 4) (Fin 4) K) (hM : (M * M : Matrix (Fin 4) (Fin 4) K) = 1)
    (hc1 : (M * rckSP4_C1 : Matrix (Fin 4) (Fin 4) K) = rckSP4_C1 * M)
    (hc2 : (M * rckSP4_C2 : Matrix (Fin 4) (Fin 4) K) = rckSP4_C2 * M)
    (hc3 : (M * rckSP4_C3 : Matrix (Fin 4) (Fin 4) K) = rckSP4_C3 * M) : M = 1 := by
  have e1e : ∀ (i j : Fin 4),
      (M * rckSP4_C1 : Matrix (Fin 4) (Fin 4) K) i j =
        (rckSP4_C1 * M : Matrix (Fin 4) (Fin 4) K) i j :=
    Matrix.ext_iff.mpr hc1
  have e2e : ∀ (i j : Fin 4),
      (M * rckSP4_C2 : Matrix (Fin 4) (Fin 4) K) i j =
        (rckSP4_C2 * M : Matrix (Fin 4) (Fin 4) K) i j :=
    Matrix.ext_iff.mpr hc2
  have e3e : ∀ (i j : Fin 4),
      (M * rckSP4_C3 : Matrix (Fin 4) (Fin 4) K) i j =
        (rckSP4_C3 * M : Matrix (Fin 4) (Fin 4) K) i j :=
    Matrix.ext_iff.mpr hc3
  have r00 : M 0 0 = M 3 2 + M 3 3 := by
    have a0 := e1e 2 0
    have a1 := e1e 3 1
    have a2 := e2e 2 0
    have a3 := e2e 2 1
    have a4 := e3e 0 1
    simp only [Matrix.mul_apply, Fin.sum_univ_four, rckSP4_C1_00, rckSP4_C1_01, rckSP4_C1_02,
      rckSP4_C1_03, rckSP4_C1_10, rckSP4_C1_11, rckSP4_C1_12, rckSP4_C1_13, rckSP4_C1_20,
      rckSP4_C1_21, rckSP4_C1_22, rckSP4_C1_23, rckSP4_C1_30, rckSP4_C1_31, rckSP4_C1_32,
      rckSP4_C1_33, rckSP4_C2_00, rckSP4_C2_01, rckSP4_C2_02, rckSP4_C2_03, rckSP4_C2_10,
      rckSP4_C2_11, rckSP4_C2_12, rckSP4_C2_13, rckSP4_C2_20, rckSP4_C2_21, rckSP4_C2_22,
      rckSP4_C2_23, rckSP4_C2_30, rckSP4_C2_31, rckSP4_C2_32, rckSP4_C2_33, rckSP4_C3_00,
      rckSP4_C3_01, rckSP4_C3_02, rckSP4_C3_03, rckSP4_C3_10, rckSP4_C3_11, rckSP4_C3_12,
      rckSP4_C3_13, rckSP4_C3_20, rckSP4_C3_21, rckSP4_C3_22, rckSP4_C3_23, rckSP4_C3_30,
      rckSP4_C3_31, rckSP4_C3_32, rckSP4_C3_33, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at a0 a1 a2 a3 a4
    linear_combination a0 + a1 + a2 + a3 + a4
      + ((M 0 0) + (M 0 1) + (M 1 0) + (M 1 1) - (M 2 2) - (M 2 3) + (M 3 1) - (M 3 2)
          - (M 3 3)) * h2
  have r01 : M 0 1 = M 3 2 := by
    have a0 := e1e 2 1
    have a1 := e1e 3 0
    have a2 := e1e 3 1
    have a3 := e2e 2 0
    simp only [Matrix.mul_apply, Fin.sum_univ_four, rckSP4_C1_00, rckSP4_C1_01, rckSP4_C1_02,
      rckSP4_C1_03, rckSP4_C1_10, rckSP4_C1_11, rckSP4_C1_12, rckSP4_C1_13, rckSP4_C1_20,
      rckSP4_C1_21, rckSP4_C1_22, rckSP4_C1_23, rckSP4_C1_30, rckSP4_C1_31, rckSP4_C1_32,
      rckSP4_C1_33, rckSP4_C2_00, rckSP4_C2_01, rckSP4_C2_02, rckSP4_C2_03, rckSP4_C2_10,
      rckSP4_C2_11, rckSP4_C2_12, rckSP4_C2_13, rckSP4_C2_20, rckSP4_C2_21, rckSP4_C2_22,
      rckSP4_C2_23, rckSP4_C2_30, rckSP4_C2_31, rckSP4_C2_32, rckSP4_C2_33, rckSP4_C3_00,
      rckSP4_C3_01, rckSP4_C3_02, rckSP4_C3_03, rckSP4_C3_10, rckSP4_C3_11, rckSP4_C3_12,
      rckSP4_C3_13, rckSP4_C3_20, rckSP4_C3_21, rckSP4_C3_22, rckSP4_C3_23, rckSP4_C3_30,
      rckSP4_C3_31, rckSP4_C3_32, rckSP4_C3_33, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at a0 a1 a2 a3
    linear_combination a0 + a1 + a2 + a3
      + ((M 0 0) + (M 0 1) + (M 1 0) + (M 1 1) - (M 2 2) - (M 2 3) - (M 3 2) - (M 3 3)) * h2
  have r02 : M 0 2 = 0 := by
    have a0 := e2e 0 1
    simp only [Matrix.mul_apply, Fin.sum_univ_four, rckSP4_C1_00, rckSP4_C1_01, rckSP4_C1_02,
      rckSP4_C1_03, rckSP4_C1_10, rckSP4_C1_11, rckSP4_C1_12, rckSP4_C1_13, rckSP4_C1_20,
      rckSP4_C1_21, rckSP4_C1_22, rckSP4_C1_23, rckSP4_C1_30, rckSP4_C1_31, rckSP4_C1_32,
      rckSP4_C1_33, rckSP4_C2_00, rckSP4_C2_01, rckSP4_C2_02, rckSP4_C2_03, rckSP4_C2_10,
      rckSP4_C2_11, rckSP4_C2_12, rckSP4_C2_13, rckSP4_C2_20, rckSP4_C2_21, rckSP4_C2_22,
      rckSP4_C2_23, rckSP4_C2_30, rckSP4_C2_31, rckSP4_C2_32, rckSP4_C2_33, rckSP4_C3_00,
      rckSP4_C3_01, rckSP4_C3_02, rckSP4_C3_03, rckSP4_C3_10, rckSP4_C3_11, rckSP4_C3_12,
      rckSP4_C3_13, rckSP4_C3_20, rckSP4_C3_21, rckSP4_C3_22, rckSP4_C3_23, rckSP4_C3_30,
      rckSP4_C3_31, rckSP4_C3_32, rckSP4_C3_33, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at a0
    linear_combination a0
  have r03 : M 0 3 = M 3 2 := by
    have a0 := e1e 2 1
    have a1 := e1e 3 0
    have a2 := e1e 3 1
    have a3 := e2e 0 0
    have a4 := e2e 0 1
    have a5 := e2e 2 0
    simp only [Matrix.mul_apply, Fin.sum_univ_four, rckSP4_C1_00, rckSP4_C1_01, rckSP4_C1_02,
      rckSP4_C1_03, rckSP4_C1_10, rckSP4_C1_11, rckSP4_C1_12, rckSP4_C1_13, rckSP4_C1_20,
      rckSP4_C1_21, rckSP4_C1_22, rckSP4_C1_23, rckSP4_C1_30, rckSP4_C1_31, rckSP4_C1_32,
      rckSP4_C1_33, rckSP4_C2_00, rckSP4_C2_01, rckSP4_C2_02, rckSP4_C2_03, rckSP4_C2_10,
      rckSP4_C2_11, rckSP4_C2_12, rckSP4_C2_13, rckSP4_C2_20, rckSP4_C2_21, rckSP4_C2_22,
      rckSP4_C2_23, rckSP4_C2_30, rckSP4_C2_31, rckSP4_C2_32, rckSP4_C2_33, rckSP4_C3_00,
      rckSP4_C3_01, rckSP4_C3_02, rckSP4_C3_03, rckSP4_C3_10, rckSP4_C3_11, rckSP4_C3_12,
      rckSP4_C3_13, rckSP4_C3_20, rckSP4_C3_21, rckSP4_C3_22, rckSP4_C3_23, rckSP4_C3_30,
      rckSP4_C3_31, rckSP4_C3_32, rckSP4_C3_33, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at a0 a1 a2 a3 a4 a5
    linear_combination a0 + a1 + a2 + a3 + a4 + a5
      + ((M 0 0) - (M 0 2) + (M 1 0) + (M 1 1) - (M 2 2) - (M 2 3) - (M 3 2) - (M 3 3)) * h2
  have r10 : M 1 0 = M 3 2 := by
    have a0 := e1e 0 0
    have a1 := e1e 2 1
    have a2 := e1e 3 0
    have a3 := e1e 3 1
    have a4 := e2e 0 0
    have a5 := e2e 0 1
    have a6 := e2e 2 0
    simp only [Matrix.mul_apply, Fin.sum_univ_four, rckSP4_C1_00, rckSP4_C1_01, rckSP4_C1_02,
      rckSP4_C1_03, rckSP4_C1_10, rckSP4_C1_11, rckSP4_C1_12, rckSP4_C1_13, rckSP4_C1_20,
      rckSP4_C1_21, rckSP4_C1_22, rckSP4_C1_23, rckSP4_C1_30, rckSP4_C1_31, rckSP4_C1_32,
      rckSP4_C1_33, rckSP4_C2_00, rckSP4_C2_01, rckSP4_C2_02, rckSP4_C2_03, rckSP4_C2_10,
      rckSP4_C2_11, rckSP4_C2_12, rckSP4_C2_13, rckSP4_C2_20, rckSP4_C2_21, rckSP4_C2_22,
      rckSP4_C2_23, rckSP4_C2_30, rckSP4_C2_31, rckSP4_C2_32, rckSP4_C2_33, rckSP4_C3_00,
      rckSP4_C3_01, rckSP4_C3_02, rckSP4_C3_03, rckSP4_C3_10, rckSP4_C3_11, rckSP4_C3_12,
      rckSP4_C3_13, rckSP4_C3_20, rckSP4_C3_21, rckSP4_C3_22, rckSP4_C3_23, rckSP4_C3_30,
      rckSP4_C3_31, rckSP4_C3_32, rckSP4_C3_33, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at a0 a1 a2 a3 a4 a5 a6
    linear_combination a0 + a1 + a2 + a3 + a4 + a5 + a6
      + ((M 0 0) - (M 0 2) - (M 0 3) + 2*(M 1 0) + (M 1 1) - (M 2 2) - (M 2 3) - (M 3 2)
          - (M 3 3)) * h2
  have r11 : M 1 1 = M 3 3 := by
    have a0 := e1e 0 1
    have a1 := e1e 2 0
    have a2 := e1e 2 1
    have a3 := e1e 3 0
    have a4 := e2e 0 0
    have a5 := e2e 2 1
    have a6 := e3e 0 1
    simp only [Matrix.mul_apply, Fin.sum_univ_four, rckSP4_C1_00, rckSP4_C1_01, rckSP4_C1_02,
      rckSP4_C1_03, rckSP4_C1_10, rckSP4_C1_11, rckSP4_C1_12, rckSP4_C1_13, rckSP4_C1_20,
      rckSP4_C1_21, rckSP4_C1_22, rckSP4_C1_23, rckSP4_C1_30, rckSP4_C1_31, rckSP4_C1_32,
      rckSP4_C1_33, rckSP4_C2_00, rckSP4_C2_01, rckSP4_C2_02, rckSP4_C2_03, rckSP4_C2_10,
      rckSP4_C2_11, rckSP4_C2_12, rckSP4_C2_13, rckSP4_C2_20, rckSP4_C2_21, rckSP4_C2_22,
      rckSP4_C2_23, rckSP4_C2_30, rckSP4_C2_31, rckSP4_C2_32, rckSP4_C2_33, rckSP4_C3_00,
      rckSP4_C3_01, rckSP4_C3_02, rckSP4_C3_03, rckSP4_C3_10, rckSP4_C3_11, rckSP4_C3_12,
      rckSP4_C3_13, rckSP4_C3_20, rckSP4_C3_21, rckSP4_C3_22, rckSP4_C3_23, rckSP4_C3_30,
      rckSP4_C3_31, rckSP4_C3_32, rckSP4_C3_33, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at a0 a1 a2 a3 a4 a5 a6
    linear_combination a0 + a1 + a2 + a3 + a4 + a5 + a6
      + (- (M 0 2) - (M 0 3) + (M 1 0) + 2*(M 1 1) - (M 2 2) - (M 2 3) + (M 3 1) - (M 3 3)) * h2
  have r12 : M 1 2 = M 3 2 := by
    have a0 := e1e 0 2
    have a1 := e1e 2 1
    have a2 := e1e 3 0
    have a3 := e1e 3 1
    have a4 := e2e 0 0
    have a5 := e2e 0 1
    have a6 := e2e 2 0
    simp only [Matrix.mul_apply, Fin.sum_univ_four, rckSP4_C1_00, rckSP4_C1_01, rckSP4_C1_02,
      rckSP4_C1_03, rckSP4_C1_10, rckSP4_C1_11, rckSP4_C1_12, rckSP4_C1_13, rckSP4_C1_20,
      rckSP4_C1_21, rckSP4_C1_22, rckSP4_C1_23, rckSP4_C1_30, rckSP4_C1_31, rckSP4_C1_32,
      rckSP4_C1_33, rckSP4_C2_00, rckSP4_C2_01, rckSP4_C2_02, rckSP4_C2_03, rckSP4_C2_10,
      rckSP4_C2_11, rckSP4_C2_12, rckSP4_C2_13, rckSP4_C2_20, rckSP4_C2_21, rckSP4_C2_22,
      rckSP4_C2_23, rckSP4_C2_30, rckSP4_C2_31, rckSP4_C2_32, rckSP4_C2_33, rckSP4_C3_00,
      rckSP4_C3_01, rckSP4_C3_02, rckSP4_C3_03, rckSP4_C3_10, rckSP4_C3_11, rckSP4_C3_12,
      rckSP4_C3_13, rckSP4_C3_20, rckSP4_C3_21, rckSP4_C3_22, rckSP4_C3_23, rckSP4_C3_30,
      rckSP4_C3_31, rckSP4_C3_32, rckSP4_C3_33, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at a0 a1 a2 a3 a4 a5 a6
    linear_combination a0 + a1 + a2 + a3 + a4 + a5 + a6
      + ((M 0 0) - (M 0 2) - (M 0 3) + (M 1 0) + (M 1 1) + (M 1 2) - (M 2 2) - (M 2 3)
          - (M 3 2) - (M 3 3)) * h2
  have r13 : M 1 3 = 0 := by
    have a0 := e1e 0 3
    simp only [Matrix.mul_apply, Fin.sum_univ_four, rckSP4_C1_00, rckSP4_C1_01, rckSP4_C1_02,
      rckSP4_C1_03, rckSP4_C1_10, rckSP4_C1_11, rckSP4_C1_12, rckSP4_C1_13, rckSP4_C1_20,
      rckSP4_C1_21, rckSP4_C1_22, rckSP4_C1_23, rckSP4_C1_30, rckSP4_C1_31, rckSP4_C1_32,
      rckSP4_C1_33, rckSP4_C2_00, rckSP4_C2_01, rckSP4_C2_02, rckSP4_C2_03, rckSP4_C2_10,
      rckSP4_C2_11, rckSP4_C2_12, rckSP4_C2_13, rckSP4_C2_20, rckSP4_C2_21, rckSP4_C2_22,
      rckSP4_C2_23, rckSP4_C2_30, rckSP4_C2_31, rckSP4_C2_32, rckSP4_C2_33, rckSP4_C3_00,
      rckSP4_C3_01, rckSP4_C3_02, rckSP4_C3_03, rckSP4_C3_10, rckSP4_C3_11, rckSP4_C3_12,
      rckSP4_C3_13, rckSP4_C3_20, rckSP4_C3_21, rckSP4_C3_22, rckSP4_C3_23, rckSP4_C3_30,
      rckSP4_C3_31, rckSP4_C3_32, rckSP4_C3_33, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at a0
    linear_combination a0 + ((M 1 3)) * h2
  have r20 : M 2 0 = 0 := by
    have a0 := e1e 0 0
    have a1 := e1e 2 0
    have a2 := e1e 2 1
    have a3 := e2e 0 0
    have a4 := e2e 0 1
    have a5 := e2e 2 1
    have a6 := e3e 0 1
    simp only [Matrix.mul_apply, Fin.sum_univ_four, rckSP4_C1_00, rckSP4_C1_01, rckSP4_C1_02,
      rckSP4_C1_03, rckSP4_C1_10, rckSP4_C1_11, rckSP4_C1_12, rckSP4_C1_13, rckSP4_C1_20,
      rckSP4_C1_21, rckSP4_C1_22, rckSP4_C1_23, rckSP4_C1_30, rckSP4_C1_31, rckSP4_C1_32,
      rckSP4_C1_33, rckSP4_C2_00, rckSP4_C2_01, rckSP4_C2_02, rckSP4_C2_03, rckSP4_C2_10,
      rckSP4_C2_11, rckSP4_C2_12, rckSP4_C2_13, rckSP4_C2_20, rckSP4_C2_21, rckSP4_C2_22,
      rckSP4_C2_23, rckSP4_C2_30, rckSP4_C2_31, rckSP4_C2_32, rckSP4_C2_33, rckSP4_C3_00,
      rckSP4_C3_01, rckSP4_C3_02, rckSP4_C3_03, rckSP4_C3_10, rckSP4_C3_11, rckSP4_C3_12,
      rckSP4_C3_13, rckSP4_C3_20, rckSP4_C3_21, rckSP4_C3_22, rckSP4_C3_23, rckSP4_C3_30,
      rckSP4_C3_31, rckSP4_C3_32, rckSP4_C3_33, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at a0 a1 a2 a3 a4 a5 a6
    linear_combination a0 + a1 + a2 + a3 + a4 + a5 + a6
      + (- (M 0 2) - (M 0 3) + (M 1 0) + (M 1 1) - (M 2 2) - (M 2 3) + (M 3 1)) * h2
  have r21 : M 2 1 = M 3 2 := by
    have a0 := e1e 0 1
    have a1 := e1e 2 0
    have a2 := e1e 2 1
    have a3 := e1e 3 0
    have a4 := e1e 3 1
    have a5 := e2e 0 0
    have a6 := e2e 2 1
    have a7 := e3e 0 0
    have a8 := e3e 0 1
    simp only [Matrix.mul_apply, Fin.sum_univ_four, rckSP4_C1_00, rckSP4_C1_01, rckSP4_C1_02,
      rckSP4_C1_03, rckSP4_C1_10, rckSP4_C1_11, rckSP4_C1_12, rckSP4_C1_13, rckSP4_C1_20,
      rckSP4_C1_21, rckSP4_C1_22, rckSP4_C1_23, rckSP4_C1_30, rckSP4_C1_31, rckSP4_C1_32,
      rckSP4_C1_33, rckSP4_C2_00, rckSP4_C2_01, rckSP4_C2_02, rckSP4_C2_03, rckSP4_C2_10,
      rckSP4_C2_11, rckSP4_C2_12, rckSP4_C2_13, rckSP4_C2_20, rckSP4_C2_21, rckSP4_C2_22,
      rckSP4_C2_23, rckSP4_C2_30, rckSP4_C2_31, rckSP4_C2_32, rckSP4_C2_33, rckSP4_C3_00,
      rckSP4_C3_01, rckSP4_C3_02, rckSP4_C3_03, rckSP4_C3_10, rckSP4_C3_11, rckSP4_C3_12,
      rckSP4_C3_13, rckSP4_C3_20, rckSP4_C3_21, rckSP4_C3_22, rckSP4_C3_23, rckSP4_C3_30,
      rckSP4_C3_31, rckSP4_C3_32, rckSP4_C3_33, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at a0 a1 a2 a3 a4 a5 a6 a7 a8
    linear_combination a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8
      + (- (M 0 2) - (M 0 3) + (M 1 0) + 2*(M 1 1) + (M 2 1) - (M 2 2) - (M 2 3) + (M 3 1)
          - (M 3 2) - (M 3 3)) * h2
  have r22 : M 2 2 = M 3 2 + M 3 3 := by
    have a0 := e1e 0 1
    have a1 := e1e 2 0
    have a2 := e1e 3 1
    have a3 := e2e 0 0
    have a4 := e2e 2 0
    simp only [Matrix.mul_apply, Fin.sum_univ_four, rckSP4_C1_00, rckSP4_C1_01, rckSP4_C1_02,
      rckSP4_C1_03, rckSP4_C1_10, rckSP4_C1_11, rckSP4_C1_12, rckSP4_C1_13, rckSP4_C1_20,
      rckSP4_C1_21, rckSP4_C1_22, rckSP4_C1_23, rckSP4_C1_30, rckSP4_C1_31, rckSP4_C1_32,
      rckSP4_C1_33, rckSP4_C2_00, rckSP4_C2_01, rckSP4_C2_02, rckSP4_C2_03, rckSP4_C2_10,
      rckSP4_C2_11, rckSP4_C2_12, rckSP4_C2_13, rckSP4_C2_20, rckSP4_C2_21, rckSP4_C2_22,
      rckSP4_C2_23, rckSP4_C2_30, rckSP4_C2_31, rckSP4_C2_32, rckSP4_C2_33, rckSP4_C3_00,
      rckSP4_C3_01, rckSP4_C3_02, rckSP4_C3_03, rckSP4_C3_10, rckSP4_C3_11, rckSP4_C3_12,
      rckSP4_C3_13, rckSP4_C3_20, rckSP4_C3_21, rckSP4_C3_22, rckSP4_C3_23, rckSP4_C3_30,
      rckSP4_C3_31, rckSP4_C3_32, rckSP4_C3_33, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at a0 a1 a2 a3 a4
    linear_combination a0 + a1 + a2 + a3 + a4
      + (- (M 0 2) - (M 0 3) + (M 1 0) + (M 1 1) - (M 2 3) - (M 3 2) - (M 3 3)) * h2
  have r23 : M 2 3 = M 3 2 := by
    have a0 := e1e 0 0
    have a1 := e1e 2 0
    have a2 := e1e 2 1
    have a3 := e1e 3 0
    have a4 := e1e 3 1
    have a5 := e2e 0 0
    have a6 := e2e 0 1
    have a7 := e2e 2 0
    simp only [Matrix.mul_apply, Fin.sum_univ_four, rckSP4_C1_00, rckSP4_C1_01, rckSP4_C1_02,
      rckSP4_C1_03, rckSP4_C1_10, rckSP4_C1_11, rckSP4_C1_12, rckSP4_C1_13, rckSP4_C1_20,
      rckSP4_C1_21, rckSP4_C1_22, rckSP4_C1_23, rckSP4_C1_30, rckSP4_C1_31, rckSP4_C1_32,
      rckSP4_C1_33, rckSP4_C2_00, rckSP4_C2_01, rckSP4_C2_02, rckSP4_C2_03, rckSP4_C2_10,
      rckSP4_C2_11, rckSP4_C2_12, rckSP4_C2_13, rckSP4_C2_20, rckSP4_C2_21, rckSP4_C2_22,
      rckSP4_C2_23, rckSP4_C2_30, rckSP4_C2_31, rckSP4_C2_32, rckSP4_C2_33, rckSP4_C3_00,
      rckSP4_C3_01, rckSP4_C3_02, rckSP4_C3_03, rckSP4_C3_10, rckSP4_C3_11, rckSP4_C3_12,
      rckSP4_C3_13, rckSP4_C3_20, rckSP4_C3_21, rckSP4_C3_22, rckSP4_C3_23, rckSP4_C3_30,
      rckSP4_C3_31, rckSP4_C3_32, rckSP4_C3_33, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at a0 a1 a2 a3 a4 a5 a6 a7
    linear_combination a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7
      + ((M 0 0) - (M 0 2) - (M 0 3) + 2*(M 1 0) + (M 1 1) - (M 2 2) - (M 2 3) - (M 3 2)
          - (M 3 3)) * h2
  have r30 : M 3 0 = M 3 2 := by
    have a0 := e1e 2 1
    have a1 := e1e 3 0
    have a2 := e1e 3 1
    have a3 := e2e 2 0
    have a4 := e3e 0 0
    simp only [Matrix.mul_apply, Fin.sum_univ_four, rckSP4_C1_00, rckSP4_C1_01, rckSP4_C1_02,
      rckSP4_C1_03, rckSP4_C1_10, rckSP4_C1_11, rckSP4_C1_12, rckSP4_C1_13, rckSP4_C1_20,
      rckSP4_C1_21, rckSP4_C1_22, rckSP4_C1_23, rckSP4_C1_30, rckSP4_C1_31, rckSP4_C1_32,
      rckSP4_C1_33, rckSP4_C2_00, rckSP4_C2_01, rckSP4_C2_02, rckSP4_C2_03, rckSP4_C2_10,
      rckSP4_C2_11, rckSP4_C2_12, rckSP4_C2_13, rckSP4_C2_20, rckSP4_C2_21, rckSP4_C2_22,
      rckSP4_C2_23, rckSP4_C2_30, rckSP4_C2_31, rckSP4_C2_32, rckSP4_C2_33, rckSP4_C3_00,
      rckSP4_C3_01, rckSP4_C3_02, rckSP4_C3_03, rckSP4_C3_10, rckSP4_C3_11, rckSP4_C3_12,
      rckSP4_C3_13, rckSP4_C3_20, rckSP4_C3_21, rckSP4_C3_22, rckSP4_C3_23, rckSP4_C3_30,
      rckSP4_C3_31, rckSP4_C3_32, rckSP4_C3_33, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at a0 a1 a2 a3 a4
    linear_combination a0 + a1 + a2 + a3 + a4
      + ((M 0 0) + (M 1 0) + (M 1 1) - (M 2 2) - (M 2 3) + (M 3 0) - (M 3 2) - (M 3 3)) * h2
  have r31 : M 3 1 = 0 := by
    have a0 := e3e 0 1
    simp only [Matrix.mul_apply, Fin.sum_univ_four, rckSP4_C1_00, rckSP4_C1_01, rckSP4_C1_02,
      rckSP4_C1_03, rckSP4_C1_10, rckSP4_C1_11, rckSP4_C1_12, rckSP4_C1_13, rckSP4_C1_20,
      rckSP4_C1_21, rckSP4_C1_22, rckSP4_C1_23, rckSP4_C1_30, rckSP4_C1_31, rckSP4_C1_32,
      rckSP4_C1_33, rckSP4_C2_00, rckSP4_C2_01, rckSP4_C2_02, rckSP4_C2_03, rckSP4_C2_10,
      rckSP4_C2_11, rckSP4_C2_12, rckSP4_C2_13, rckSP4_C2_20, rckSP4_C2_21, rckSP4_C2_22,
      rckSP4_C2_23, rckSP4_C2_30, rckSP4_C2_31, rckSP4_C2_32, rckSP4_C2_33, rckSP4_C3_00,
      rckSP4_C3_01, rckSP4_C3_02, rckSP4_C3_03, rckSP4_C3_10, rckSP4_C3_11, rckSP4_C3_12,
      rckSP4_C3_13, rckSP4_C3_20, rckSP4_C3_21, rckSP4_C3_22, rckSP4_C3_23, rckSP4_C3_30,
      rckSP4_C3_31, rckSP4_C3_32, rckSP4_C3_33, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at a0
    linear_combination a0 + ((M 3 1)) * h2
  have hb2 : M 3 2 * M 3 2 = 0 := by
    have h := Matrix.ext_iff.mpr hM 0 1
    simp [Matrix.mul_apply, Fin.sum_univ_four] at h
    simp only [r00, r01, r02, r03, r11, r21, r31] at h
    linear_combination h - (M 3 2 * M 3 3) * h2
  have hb0 : M 3 2 = 0 := mul_self_eq_zero.mp hb2
  have ha2 : M 3 3 * M 3 3 = 1 := by
    have h := Matrix.ext_iff.mpr hM 0 0
    simp [Matrix.mul_apply, Fin.sum_univ_four] at h
    simp only [r00, r01, r02, r03, r10, r11, r20, r30] at h
    linear_combination h - 3 * hb2 - (M 3 2 * M 3 3) * h2
  have ha1 : M 3 3 = 1 := by
    have h : (M 3 3 - 1) * (M 3 3 - 1) = 0 := by
      linear_combination ha2 - (M 3 3 - 1) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h)
  simp only [hb0, ha1] at r00 r01 r02 r03 r10 r11 r12 r13 r20 r21 r22 r23 r30 r31
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.one_apply, hb0, ha1, r00, r01, r02, r03, r10, r11, r12, r13, r20, r21,
      r22, r23, r30, r31]

end CFSG.StandardType.RCKFlag
