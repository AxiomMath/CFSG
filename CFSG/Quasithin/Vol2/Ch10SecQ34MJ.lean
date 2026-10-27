module

public import CFSG.Quasithin.Vol2.Ch10SecQ34MI

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Quasithin Matrix

variable {K : Type} [Field K] [CharP K 2] (a : ℕ)

@[expose] def um (t : K) : Matrix (Fin 2) (Fin 2) K := !![1, t; 0, 1]

@[expose] def wm : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

@[expose] def e11 (c : K) : Matrix (Fin 2) (Fin 2) K := !![c, 0; 0, 0]

@[expose] def e22 (c : K) : Matrix (Fin 2) (Fin 2) K := !![0, 0; 0, c]

@[expose] def om (t : K) : Matrix (Fin 2) (Fin 2) K := !![0, t; t ^ 2 ^ a, 0]

omit [CharP K 2] in
theorem tw_u (t : K) (X : Matrix (Fin 2) (Fin 2) K) :
    tw a (um t) X = !![X 0 0 + t * X 1 0 + (X 0 1 + t * X 1 1) * t ^ 2 ^ a,
      X 0 1 + t * X 1 1; X 1 0 + X 1 1 * t ^ 2 ^ a, X 1 1] := by
  have h2 : (2 ^ a : ℕ) ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tw, um, frobPow, Matrix.mul_apply, Fin.sum_univ_two, zero_pow h2, Matrix.vecMul,
      dotProduct]

omit [CharP K 2] in
theorem tw_w (X : Matrix (Fin 2) (Fin 2) K) :
    tw a wm X = !![X 1 1, X 1 0; X 0 1, X 0 0] := by
  have h2 : (2 ^ a : ℕ) ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tw, wm, frobPow, Matrix.mul_apply, Fin.sum_univ_two,
    zero_pow h2, Matrix.vecMul, dotProduct]

omit [CharP K 2] in
theorem tw_u_e11 (t c : K) : tw a (um t) (e11 c) = e11 c := by
  rw [tw_u]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e11]

omit [CharP K 2] in
theorem tw_w_e11 (c : K) : tw a wm (e11 c) = e22 c := by
  rw [tw_w]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e11, e22]

theorem tw_u_e22 (t c : K) :
    tw a (um t) (e22 c) + e22 c = !![t * c * t ^ 2 ^ a, t * c; c * t ^ 2 ^ a, 0] := by
  rw [tw_u]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e22, CharTwo.add_self_eq_zero]

theorem tw_u_aux (t c : K) :
    tw a (um 1) !![t * c * t ^ 2 ^ a, t * c; c * t ^ 2 ^ a, 0] +
      !![t * c * t ^ 2 ^ a, t * c; c * t ^ 2 ^ a, 0] = e11 (c * (t + t ^ 2 ^ a)) := by
  rw [tw_u]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e11, CharTwo.add_self_eq_zero]
  linear_combination (t * c * t ^ 2 ^ a) * (CharTwo.two_eq_zero (R := K))

theorem eq_e11_of_fixed [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a))
    {Z : Matrix (Fin 2) (Fin 2) K} (hZ : IsHerm a Z) (hfix : ∀ t, tw a (um t) Z = Z) :
    Z = e11 (Z 0 0) := by
  obtain ⟨t₁, ht₁⟩ := exists_trace_eq_one a ha hK
  have hZ' := (isHerm_iff a Z).mp hZ
  have h1 := hfix 1
  rw [tw_u] at h1
  have e01 := congrFun (congrFun h1 0) 1
  have e00 := congrFun (congrFun h1 0) 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, one_mul, one_pow, mul_one] at e01 e00
  have h11 : Z 1 1 = 0 := by linear_combination e01
  rw [h11, add_zero] at e00
  have h10 : Z 1 0 = Z 0 1 := by
    have h' : Z 1 0 + Z 0 1 = 0 := by linear_combination e00
    rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
    exact h'
  have h2 := hfix t₁
  rw [tw_u] at h2
  have f00 := congrFun (congrFun h2 0) 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one] at f00
  rw [h11, mul_zero, add_zero, h10] at f00
  have h01 : Z 0 1 = 0 := by linear_combination f00 - Z 0 1 * ht₁
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e11, h01, h11, h10]

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
