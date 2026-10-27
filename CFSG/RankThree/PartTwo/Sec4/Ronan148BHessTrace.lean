module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.CharP

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem trace_eq_of_pow_char_eq_one {m : ℕ} [NeZero m] {X : Matrix (Fin m) (Fin m) K}
    (hX : X ^ p = 1) : X.trace = m := by
  have h0 : (X - 1) ^ p = 0 := by
    rw [sub_pow_char_of_commute (p := p) (Commute.one_right X), hX, one_pow,
      sub_self]
  have hnil : IsNilpotent (X - 1) := ⟨p, h0⟩
  have ht := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin] at ht
  linear_combination ht

theorem trace_eq_two_or_neg_two (hp2 : p ≠ 2) {C : Matrix (Fin 2) (Fin 2) K} (hdet : C.det = 1)
    (hC : C ^ (2 * p) = 1) : C.trace = 2 ∨ C.trace = -2 := by
  have h2 : (C ^ 2) ^ p = 1 := by rw [← pow_mul, hC]
  have htr := trace_eq_of_pow_char_eq_one (p := p) h2
  have hsq : (C ^ 2).trace = C.trace ^ 2 - 2 * C.det := by
    rw [sq, Matrix.trace_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hsq, hdet] at htr
  have h4 : (C.trace - 2) * (C.trace + 2) = 0 := by
    push_cast at htr
    linear_combination htr
  rcases mul_eq_zero.mp h4 with h | h
  · exact Or.inl (by linear_combination h)
  · exact Or.inr (by linear_combination h)

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
