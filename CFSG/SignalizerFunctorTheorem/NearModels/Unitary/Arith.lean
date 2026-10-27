module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public section

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut

theorem ne_two_ne_three_not_dvd_of_coprime {p : ℕ} (hp : p.Prime)
    (h : UnitaryFieldData 2 p (GaloisField 2 (2 * p)))
    (hcop : Nat.Coprime p (Nat.card (hypPSU h 1 1))) :
    p ≠ 2 ∧ p ≠ 3 ∧ ¬ p ∣ Nat.card (hypSU h 1 1) := by
  have hmul := card_hypPSU_mul h (r := 1) (ε := 1)
  have hZ := card_hypScalars h (r := 1) (ε := 1) (by omega)
  have hS := (card_hypSU h (r := 1) (ε := 1) (by omega)).1
  have hS' : (Nat.card (hypSU h 1 1) : ℤ) =
      ((2 ^ p : ℕ) : ℤ) ^ 3 * ((((2 ^ p : ℕ) : ℤ) ^ 2 - 1) * (((2 ^ p : ℕ) : ℤ) ^ 3 + 1)) := by
    rw [hS]
    have : Finset.Icc 2 (2 * 1 + 1) = {2, 3} := by decide
    rw [this, Finset.prod_pair (by norm_num)]
    norm_num
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hZ1 : Nat.card (hypScalars h 1 1) = 1 := by rw [hZ]; norm_num
    have hS1 : Nat.card (hypSU h 1 1) = 62400 := by
      have := hS'
      norm_num at this
      exact_mod_cast this
    rw [hZ1, mul_one, hS1] at hmul
    rw [hmul] at hcop
    revert hcop
    norm_num
  have hp3 : p ≠ 3 := by
    rintro rfl
    have hZ1 : Nat.card (hypScalars h 1 1) = 3 := by rw [hZ]; norm_num
    have hS1 : Nat.card (hypSU h 1 1) = 16547328 := by
      have := hS'
      norm_num at this
      exact_mod_cast this
    rw [hZ1, hS1] at hmul
    have hX : Nat.card (hypPSU h 1 1) = 5515776 := by omega
    rw [hX] at hcop
    revert hcop
    norm_num
  refine ⟨hp2, hp3, ?_⟩
  have hZp : ¬ p ∣ Nat.card (hypScalars h 1 1) := by
    rw [hZ]
    intro hd
    have : p ∣ 3 := hd.trans (Nat.gcd_dvd_left _ _)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this)
  have hX : ¬ p ∣ Nat.card (hypPSU h 1 1) := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  rw [← hmul]
  intro hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
  · exact hX h1
  · exact hZp h1

end CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut
