module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartOne.A6N

open Matrix

variable {K : Type*} [Field K]

theorem ch3 (u : Matrix (Fin 3) (Fin 3) K) :
    u * u * u - u.trace • (u * u) +
      ((u 0 0 * u 1 1 - u 0 1 * u 1 0) + (u 0 0 * u 2 2 - u 0 2 * u 2 0) +
        (u 1 1 * u 2 2 - u 1 2 * u 2 1)) • u - u.det • (1 : Matrix (Fin 3) (Fin 3) K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.trace, Matrix.det_fin_three] <;> ring

theorem tr_sq_eq (u : Matrix (Fin 3) (Fin 3) K) :
    (u * u).trace = u.trace ^ 2 - 2 * ((u 0 0 * u 1 1 - u 0 1 * u 1 0) +
      (u 0 0 * u 2 2 - u 0 2 * u 2 0) + (u 1 1 * u 2 2 - u 1 2 * u 2 1)) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem tr_adjugate (u : Matrix (Fin 3) (Fin 3) K) :
    u.adjugate.trace = (u 0 0 * u 1 1 - u 0 1 * u 1 0) +
      (u 0 0 * u 2 2 - u 0 2 * u 2 0) + (u 1 1 * u 2 2 - u 1 2 * u 2 1) := by
  rw [Matrix.adjugate_fin_three]
  simp [Matrix.trace, Fin.sum_univ_three]
  ring

@[expose] def e2 (u : Matrix (Fin 3) (Fin 3) K) : K :=
  (u 0 0 * u 1 1 - u 0 1 * u 1 0) + (u 0 0 * u 2 2 - u 0 2 * u 2 0) +
    (u 1 1 * u 2 2 - u 1 2 * u 2 1)

theorem tr_sq_ne (h5 : (5 : K) ≠ 0) {u : Matrix (Fin 3) (Fin 3) K} (hdet : u.det = 1)
    (hu5 : u ^ 5 = 1) (hu1 : u ≠ 1) (htr : u⁻¹.trace = u.trace) :
    (u ^ 2).trace ≠ u.trace := by
  intro hsq
  have hinv : u⁻¹ = u.adjugate := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  have he : e2 u = u.trace := by
    rw [← htr, hinv, tr_adjugate]
    rfl
  have hsq2 : (u ^ 2).trace = u.trace ^ 2 - 2 * u.trace := by
    rw [pow_two, tr_sq_eq]
    change u.trace ^ 2 - 2 * e2 u = _
    rw [he]
  have hch := ch3 u
  change u * u * u - u.trace • (u * u) + e2 u • u - u.det • (1 : Matrix (Fin 3) (Fin 3) K) = 0 at hch
  rw [he, hdet, one_smul] at hch
  have ht : u.trace = 0 ∨ u.trace = 3 := by
    have : u.trace * (u.trace - 3) = 0 := by linear_combination hsq2.symm.trans hsq
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rcases ht with h0 | h3
  ·
    rw [h0, zero_smul, sub_zero, zero_smul, add_zero] at hch
    have hu3 : u * u * u = 1 := sub_eq_zero.1 hch
    have hu5' : u * u * u * u * u = 1 := by simpa [pow_succ, mul_assoc] using hu5
    have hu2 : u * u = 1 := by
      rw [hu3] at hu5'
      simpa [mul_assoc] using hu5'
    apply hu1
    calc u = u * (u * u) := by rw [hu2, mul_one]
      _ = u * u * u := by rw [mul_assoc]
      _ = 1 := hu3
  ·
    have cancel5 : ∀ X : Matrix (Fin 3) (Fin 3) K, (5 : ℕ) • X = 0 → X = 0 := fun X hX => by
      have h : ((5 : ℕ) : K) • X = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hX
      exact (smul_eq_zero.1 h).resolve_left (by simpa using h5)
    set n : Matrix (Fin 3) (Fin 3) K := u - 1 with hn
    have hu : u = 1 + n := by rw [hn]; abel
    have hch' : u * u * u - (3 : ℕ) • (u * u) + (3 : ℕ) • u - 1 = 0 := by
      rw [h3] at hch
      simpa [← Nat.cast_smul_eq_nsmul K] using hch
    have hn3 : n * n * n = 0 := by
      have : n * n * n = u * u * u - (3 : ℕ) • (u * u) + (3 : ℕ) • u - 1 := by
        rw [hn]; noncomm_ring
      rw [this]
      exact hch'
    have h5'' : u ^ 5 - 1 = (5 : ℕ) • n + (10 : ℕ) • (n * n) + (10 : ℕ) • (n * n * n) +
        (5 : ℕ) • (n * n * n * n) + n * n * n * n * n := by
      rw [hu]; noncomm_ring
    rw [hu5, sub_self] at h5''
    simp only [hn3, smul_zero, zero_mul, add_zero] at h5''
    have hE : (5 : ℕ) • n + (10 : ℕ) • (n * n) = 0 := h5''.symm
    have hnn : n * n = 0 := by
      have h6 : n * ((5 : ℕ) • n + (10 : ℕ) • (n * n)) = (5 : ℕ) • (n * n) +
          (10 : ℕ) • (n * n * n) := by noncomm_ring
      rw [hE, mul_zero, hn3, smul_zero, add_zero] at h6
      exact cancel5 _ h6.symm
    have hn0 : n = 0 := by
      rw [hnn, smul_zero, add_zero] at hE
      exact cancel5 _ hE
    apply hu1
    rw [hu, hn0, add_zero]

end CFSG.RankThree.PartOne.A6N
