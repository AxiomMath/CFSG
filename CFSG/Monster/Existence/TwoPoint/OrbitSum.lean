module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

public section

namespace CFSG.Monster.Existence

open Finset

theorem eq_of_sum_div_eq_sum_div {ι : Type*} (S : Finset ι) {N : ℕ} {s h : ι → ℕ} (hN : 0 < N)
    (hs : ∀ i ∈ S, s i ∣ N) (hh : ∀ i ∈ S, h i ∣ N) (hpos : ∀ i ∈ S, 0 < h i)
    (hle : ∀ i ∈ S, h i ≤ s i) (hsum : ∑ i ∈ S, N / s i = ∑ i ∈ S, N / h i) :
    ∀ i ∈ S, s i = h i := by
  have hdiv : ∀ i ∈ S, N / s i ≤ N / h i := fun i hi =>
    Nat.div_le_div_left (hle i hi) (hpos i hi)
  have heq := (Finset.sum_eq_sum_iff_of_le hdiv).1 hsum
  intro i hi
  have e1 : N / s i * s i = N := Nat.div_mul_cancel (hs i hi)
  have e2 : N / h i * h i = N := Nat.div_mul_cancel (hh i hi)
  have hq : 0 < N / h i := Nat.div_pos (Nat.le_of_dvd hN (hh i hi)) (hpos i hi)
  rw [heq i hi] at e1
  exact Nat.eq_of_mul_eq_mul_left hq (e1.trans e2.symm)

end CFSG.Monster.Existence
