module

public import CFSG.RankThree.GroupTheory.SteinbergBMExceptionalComponentCentralization

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem not_sq_dvd_card_mulAut_J3 {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ p ^ 2 ∣ 100465920 := by
  intro h
  have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have h3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
  have hc : Nat.Coprime (p ^ 2) (2 ^ 8 * 3 ^ 5) :=
    Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right (Nat.Coprime.pow_right 8 h2)
      (Nat.Coprime.pow_right 5 h3))
  have h0 : p ^ 2 ∣ 1615 * (2 ^ 8 * 3 ^ 5) := by
    have e : (1615 * (2 ^ 8 * 3 ^ 5) : ℕ) = 100465920 := by norm_num
    rw [e]
    exact h
  have h' : p ^ 2 ∣ 1615 := hc.dvd_of_dvd_mul_right h0
  have hle : p ^ 2 ≤ 1615 := Nat.le_of_dvd (by norm_num) h'
  have hp40 : p ≤ 40 := by nlinarith
  interval_cases p <;> norm_num at h'

end CFSG.RankThree.GroupTheory.SteinbergBM
