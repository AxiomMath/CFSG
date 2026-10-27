module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix

variable {F : Type*} [Field F]

@[expose] def gAlg1 : Matrix (Fin 2) (Fin 2) F := !![-1, 0; 0, 1]

@[expose] def gAlg2 (i : F) : Matrix (Fin 2) (Fin 2) F := !![i, 0; 0, 1]

@[expose] def gAlg2' (i : F) : Matrix (Fin 2) (Fin 2) F := !![-i, 0; 0, 1]

@[expose] def gAlg3 (i : F) : Matrix (Fin 2) (Fin 2) F := !![1 + i, 1 + i; -(1 - i), 1 - i]

@[expose] def gAlg3' (i : F) : Matrix (Fin 2) (Fin 2) F := !![1 - i, -(1 + i); 1 - i, 1 + i]

theorem gAlg1_mul : (gAlg1 : Matrix (Fin 2) (Fin 2) F) * gAlg1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gAlg1, Matrix.mul_apply, Fin.sum_univ_two]

theorem gAlg2'_mul {i : F} (hi : i ^ 2 = -1) : gAlg2' i * gAlg2 i = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gAlg2, gAlg2', Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination -hi

theorem gAlg3'_mul {i : F} (h3 : (3 : F) = 0) (hi : i ^ 2 = -1) : gAlg3' i * gAlg3 i = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gAlg3, gAlg3', Matrix.mul_apply, Fin.sum_univ_two] <;>
    (first | ring1 | linear_combination h3 - 2 * hi)

theorem involution_gu2_eq {i : F} (h3 : (3 : F) = 0) (hi : i ^ 2 = -1)
    {A : Matrix (Fin 2) (Fin 2) F} (hA : A * A = 1)
    (h1 : A * (gAlg1 * A * gAlg1) = (gAlg1 * A * gAlg1) * A)
    (h2 : A * (gAlg2 i * A * gAlg2' i) = (gAlg2 i * A * gAlg2' i) * A)
    (h3' : A * (gAlg3 i * A * gAlg3' i) = (gAlg3 i * A * gAlg3' i) * A) : A = 1 ∨ A = -1 := by
  have h2ne : (2 : F) ≠ 0 := fun h => one_ne_zero (show (1 : F) = 0 by linear_combination h3 - h)
  have hi0 : i ≠ 0 := fun h => by
    rw [h] at hi
    simp at hi
  have hep : (1 + i) ≠ 0 := fun h => by
    have hm : i = -1 := by linear_combination h
    rw [hm] at hi
    exact h2ne (by linear_combination hi)
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, A = !![a, b; c, d] :=
    ⟨A 0 0, A 0 1, A 1 0, A 1 1, Matrix.eta_fin_two A⟩
  have p00 := congrFun (congrFun hA 0) 0
  have p01 := congrFun (congrFun hA 0) 1
  have p10 := congrFun (congrFun hA 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at p00 p01 p10
  have q01 := congrFun (congrFun h1 0) 1
  have q10 := congrFun (congrFun h1 1) 0
  simp [gAlg1, Matrix.mul_apply, Fin.sum_univ_two] at q01 q10
  have r00 := congrFun (congrFun h2 0) 0
  simp [gAlg2, gAlg2', Matrix.mul_apply, Fin.sum_univ_two] at r00
  have s01 := congrFun (congrFun h3' 0) 1
  simp [gAlg3, gAlg3', Matrix.mul_apply, Fin.sum_univ_two] at s01
  by_cases hda : d = a
  · subst hda
    have hab : d * b = 0 := by
      have : 2 * (d * b) = 0 := by linear_combination p01
      exact (mul_eq_zero.mp this).resolve_left h2ne
    have hca : c * d = 0 := by
      have : 2 * (c * d) = 0 := by linear_combination p10
      exact (mul_eq_zero.mp this).resolve_left h2ne
    by_cases ha0 : d = 0
    · exfalso
      subst ha0
      have hbc : b * c = 1 := by linear_combination p00
      have h2i : 2 * i * (b * c) = 0 := by linear_combination -r00
      rw [hbc, mul_one] at h2i
      exact hi0 ((mul_eq_zero.mp h2i).resolve_left h2ne)
    · have hb : b = 0 := (mul_eq_zero.mp hab).resolve_left ha0
      have hc : c = 0 := (mul_eq_zero.mp hca).resolve_right ha0
      subst hb hc
      have hd : (d - 1) * (d + 1) = 0 := by linear_combination p00
      rcases mul_eq_zero.mp hd with h | h
      · left
        have : d = 1 := by linear_combination h
        subst this
        ext x y
        fin_cases x <;> fin_cases y <;> simp
      · right
        have : d = -1 := by linear_combination h
        subst this
        ext x y
        fin_cases x <;> fin_cases y <;> simp
  · exfalso
    have hb : b = 0 := by
      have : 2 * (b * (d - a)) = 0 := by linear_combination q01
      exact (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2ne)).resolve_right
        (sub_ne_zero.mpr hda)
    have hc : c = 0 := by
      have : 2 * (c * (d - a)) = 0 := by linear_combination -q10
      exact (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2ne)).resolve_right
        (sub_ne_zero.mpr hda)
    subst hb hc
    have hs : ((a - d) * (1 + i)) ^ 2 = 0 := by linear_combination -s01
    exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hda)) hep (pow_eq_zero_iff (two_ne_zero) |>.mp hs)

end CFSG.Quasithin.E2P.Asc80
