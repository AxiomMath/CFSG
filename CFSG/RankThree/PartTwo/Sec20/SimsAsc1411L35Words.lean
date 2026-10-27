module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix

variable {K : Type} [Field K]

@[expose] def l35X : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, -1, 1; 1, 1, 0]

theorem transpose_l35X : (l35X : Matrix (Fin 3) (Fin 3) K)ᵀ = l35X := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_l35X : (l35X : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [l35X, Matrix.det_fin_three]

theorem l35X_pow_thirtyTwo (h5 : (5 : K) = 0) :
    (l35X : Matrix (Fin 3) (Fin 3) K) ^ 32 = l35X := by
  have e2 : (l35X : Matrix (Fin 3) (Fin 3) K) ^ 2 = !![1, 1, 0; 1, 2, -1; 0, -1, 2] := by
    rw [sq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [l35X, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e4 : (l35X : Matrix (Fin 3) (Fin 3) K) ^ 4 = !![2, -2, -1; -2, 1, 1; -1, 1, 0] := by
    rw [show 4 = 2 + 2 from rfl, pow_add, e2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e8 : (l35X : Matrix (Fin 3) (Fin 3) K) ^ 8 = !![-1, -2, 1; -2, 1, -2; 1, -2, 2] := by
    rw [show 8 = 4 + 4 from rfl, pow_add, e4]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e16 : (l35X : Matrix (Fin 3) (Fin 3) K) ^ 16 = !![1, -2, 0; -2, -1, 2; 0, 2, -1] := by
    rw [show 16 = 8 + 8 from rfl, pow_add, e8]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  rw [show 32 = 16 + 16 from rfl, pow_add, e16]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l35X, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

@[expose] def l35T : Matrix (Fin 3) (Fin 3) K := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

@[expose] def l35E (a b : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, a; 0, 1, b; 0, 0, 1]

theorem l35T_mul_self : (l35T : Matrix (Fin 3) (Fin 3) K) * l35T = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l35T, Matrix.mul_apply, Fin.sum_univ_three]

theorem l35E_mul (a b c d : K) : l35E a b * l35E c d = l35E (a + c) (b + d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l35E, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem l35E_zero : (l35E 0 0 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l35E]

theorem det_l35E (a b : K) : (l35E a b).det = 1 := by
  simp [l35E, Matrix.det_fin_three]

theorem l35E_injective : Function.Injective fun ab : K × K => l35E ab.1 ab.2 := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have e1 := congrFun (congrFun h 0) 2
  have e2 := congrFun (congrFun h 1) 2
  simp only [l35E, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons] at e1 e2
  rw [e1, e2]

theorem l35T_conj_l35X₁ (h5 : (5 : K) = 0) :
    (l35T : Matrix (Fin 3) (Fin 3) K) * l35E 2 0 * l35T * l35E (-2) 0 = l35E 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l35T, l35E, Matrix.mul_apply, Fin.sum_univ_three] <;>
    grind

theorem l35T_conj_l35X₂ (h5 : (5 : K) = 0) :
    (l35T : Matrix (Fin 3) (Fin 3) K) * l35E 0 2 * l35T * l35E 0 (-2) = l35E 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l35T, l35E, Matrix.mul_apply, Fin.sum_univ_three] <;>
    grind

end CFSG.RankThree.PartTwo.Sec20
