module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res6ProofMat

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130Res7Proof

open Matrix
open CFSG.RankThree.PartTwo.Sec21.Item2130Res6Proof (mul_apply_of_distinct
  eq_or_eq_or_eq_of_distinct)

variable {K : Type} [Field K]

theorem mul_mul_eq_zero_of_block {N N' : Matrix (Fin 3) (Fin 3) K} {δ : Fin 3 → K}
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hij0 : N i j = 0)
    (hji0 : N j i = 0) (hconj : N' * diagonal δ = diagonal δ * N) (hcomm : N * N' = N' * N) :
    N j k * N k j * (δ k ^ 2 - δ j ^ 2) = 0 := by
  have e := fun (a b : Matrix (Fin 3) (Fin 3) K) r s => mul_apply_of_distinct a b hij hik hjk r s
  have h1 := congrFun (congrFun hcomm j) j
  rw [e, e, hji0, hij0] at h1
  have h1' : N j k * N' k j = N' j k * N k j := by linear_combination h1
  have h2 := congrFun (congrFun hconj k) j
  have h3 := congrFun (congrFun hconj j) k
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h2 h3
  linear_combination (δ j * δ k) * h1' + (-(N j k * δ k)) * h2 + (N k j * δ j) * h3

theorem eq_zero_of_unitary_block (σ : K →+* K) {N : Matrix (Fin 3) (Fin 3) K}
    (hN : (N.map σ)ᵀ * N = 1) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hij0 : N i j = 0) (hik0 : N i k = 0) (hrs : N j k * N k j = 0) :
    N j k = 0 ∧ N k j = 0 := by
  have e := fun r s => mul_apply_of_distinct ((N.map σ)ᵀ) N hij hik hjk r s
  have hjj := congrFun (congrFun hN j) j
  have hjk' := congrFun (congrFun hN j) k
  have hkk := congrFun (congrFun hN k) k
  rw [e] at hjj hjk' hkk
  simp only [Matrix.transpose_apply, Matrix.map_apply, hij0, hik0, map_zero, zero_mul, zero_add,
    Matrix.one_apply_eq, Matrix.one_apply_ne hjk] at hjj hjk' hkk
  rcases mul_eq_zero.mp hrs with h | h
  · refine ⟨h, ?_⟩
    rw [h, map_zero, zero_mul, zero_add] at hkk
    have hkk0 : N k k ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hkk
      exact zero_ne_one hkk
    rw [h, mul_zero, zero_add] at hjk'
    exact (map_eq_zero σ).mp ((mul_eq_zero.mp hjk').resolve_right hkk0)
  · refine ⟨?_, h⟩
    rw [h, map_zero, zero_mul, add_zero] at hjj
    have hjj0 : σ (N j j) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hjj
      exact zero_ne_one hjj
    rw [h, map_zero, zero_mul, add_zero] at hjk'
    exact (mul_eq_zero.mp hjk').resolve_left hjj0

theorem commute_diagonal_of_block {N : Matrix (Fin 3) (Fin 3) K} {δ : Fin 3 → K} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hij0 : N i j = 0) (hik0 : N i k = 0)
    (hji0 : N j i = 0) (hki0 : N k i = 0) (hδ : δ j = δ k) :
    N * diagonal δ = diagonal δ * N := by
  ext r s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases eq_or_eq_or_eq_of_distinct i j k r hij hik hjk with rfl | rfl | rfl <;>
    rcases eq_or_eq_or_eq_of_distinct _ _ _ s hij hik hjk with rfl | rfl | rfl <;>
    simp only [hij0, hik0, hji0, hki0, hδ, mul_zero, mul_comm]

theorem isDiag_of_block {N : Matrix (Fin 3) (Fin 3) K} {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hij0 : N i j = 0) (hik0 : N i k = 0) (hji0 : N j i = 0)
    (hki0 : N k i = 0) (hjk0 : N j k = 0) (hkj0 : N k j = 0) : N.IsDiag := by
  intro r s hrs
  rcases eq_or_eq_or_eq_of_distinct i j k r hij hik hjk with rfl | rfl | rfl <;>
    rcases eq_or_eq_or_eq_of_distinct _ _ _ s hij hik hjk with rfl | rfl | rfl <;>
    first | exact absurd rfl hrs | assumption

theorem eq_of_sq_eq_of_cube {l a b : K} (hl : l ≠ 0) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (h : (l * a) ^ 2 = (l * b) ^ 2) : l * a = l * b := by
  have ha0 : a ≠ 0 := fun h0 => by
    rw [h0] at ha
    norm_num at ha
  have hab : a ^ 2 = b ^ 2 := by
    have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
    rw [mul_pow, mul_pow] at h
    exact mul_left_cancel₀ hl2 h
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha0
  have e1 : a = a ^ 3 / a ^ 2 := by field_simp
  have e2 : b = b ^ 3 / b ^ 2 := by
    have hb0 : b ^ 2 ≠ 0 := hab ▸ ha2
    field_simp
  rw [e1, e2, ha, hb, hab]

end CFSG.RankThree.PartTwo.Sec21.Item2130Res7Proof
