module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type} [Field K]

private theorem card_hypSU_two_zero_nat (h : UnitaryFieldData 2 n K) :
    Nat.card (hypSU h 2 0) = (2 ^ n) ^ 6 *
      (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1)) := by
  have h1 := (card_hypSU h (r := 2) (ε := 0) (by norm_num)).1
  have hIcc : Finset.Icc 2 4 = {2, 3, 4} := by decide
  rw [hIcc] at h1
  norm_num at h1
  apply (Nat.cast_inj (R := ℤ)).mp
  have hp2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow 2 _ (by positivity)
  have hp4 : 1 ≤ (2 ^ n) ^ 4 := Nat.one_le_pow 4 _ (by positivity)
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [Nat.cast_sub hp2, Nat.cast_sub hp4]
  rw [h1]
  push_cast
  ring

theorem three_dvd_two_pow_sub_one (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨m, rfl⟩ := hn
  have h : 2 ^ (m + m) = 4 ^ m := by
    rw [← two_mul, pow_mul]
    norm_num
  rw [h]
  exact Nat.sub_one_dvd_pow_sub_one 4 m

theorem one_le_factorization_card_units (h : UnitaryFieldData 2 n K) :
    1 ≤ (Nat.card Kˣ).factorization 3 := by
  have hK : Nat.card K = 4 ^ n := by
    rw [h.card, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hne : 4 ^ n - 1 ≠ 0 := by
    have h1 : 1 < 4 ^ n := Nat.one_lt_pow (by have := h.one_le; omega) (by norm_num)
    omega
  have hdvd : 3 ∣ 4 ^ n - 1 := Nat.sub_one_dvd_pow_sub_one 4 n
  have hpos : 0 < (4 ^ n - 1).factorization 3 :=
    Nat.prime_three.factorization_pos_of_dvd hne hdvd
  rw [Nat.card_units, hK]
  exact hpos

theorem three_pow_factorization_dvd (h : UnitaryFieldData 2 n K) (hn : Even n) :
    3 ^ (Nat.card Kˣ).factorization 3 ∣ 2 ^ n - 1 := by
  have hqmod : (2 ^ n) % 3 = 1 := by
    obtain ⟨m, hm⟩ := hn
    rw [hm, ← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have hnot : ¬ 3 ∣ 2 ^ n + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hqmod]
    norm_num
  have hKcard : Nat.card Kˣ = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [Nat.card_units, h.card, show 2 * n = n * 2 by omega, pow_mul,
      ← Nat.sq_sub_sq, one_pow]
  have hne1 : 2 ^ n + 1 ≠ 0 := by positivity
  have hne2 : 2 ^ n - 1 ≠ 0 := by
    have h1 : 1 < 2 ^ n := Nat.one_lt_pow (by have := h.one_le; omega) (by norm_num)
    omega
  have hfac : (Nat.card Kˣ).factorization 3 = (2 ^ n - 1).factorization 3 := by
    rw [hKcard, Nat.factorization_mul hne1 hne2, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnot, zero_add]
  rw [hfac]
  exact Nat.ordProj_dvd (2 ^ n - 1) 3

theorem factorization_card_hypSU_two_zero (h : UnitaryFieldData 2 n K) (hn : Even n) :
    (Nat.card (hypSU h 2 0)).factorization 3 = 2 * (Nat.card Kˣ).factorization 3 := by
  have hqmod : (2 ^ n) % 3 = 1 := by
    obtain ⟨m, hm⟩ := hn
    rw [hm, ← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have hq0 : 2 ^ n ≠ 0 := by positivity
  have hq1 : 1 < 2 ^ n := Nat.one_lt_pow (by have := h.one_le; omega) (by norm_num)
  have h3q : ¬ 3 ∣ 2 ^ n := by
    rw [Nat.dvd_iff_mod_eq_zero, hqmod]
    norm_num
  have h3q3 : ¬ 3 ∣ (2 ^ n) ^ 3 + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, hqmod]
    norm_num
  have h3q2p : ¬ 3 ∣ (2 ^ n) ^ 2 + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, hqmod]
    norm_num
  have h3q6 : ¬ 3 ∣ (2 ^ n) ^ 6 := fun hd =>
    h3q (Nat.prime_three.dvd_of_dvd_pow hd)
  have h2m : (2 ^ n) ^ 2 - 1 ≠ 0 := by
    have h : 1 < (2 ^ n) ^ 2 := Nat.one_lt_pow (by norm_num) hq1
    omega
  have h2p : (2 ^ n) ^ 2 + 1 ≠ 0 := by positivity
  have h3p : (2 ^ n) ^ 3 + 1 ≠ 0 := by positivity
  have h4n : (2 ^ n) ^ 4 - 1 ≠ 0 := by
    have h : 1 < (2 ^ n) ^ 4 := Nat.one_lt_pow (by norm_num) hq1
    omega
  have h4eq : (2 ^ n) ^ 4 - 1 = ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 2 + 1) := by
    have hpow : (2 ^ n) ^ 4 = ((2 ^ n) ^ 2) ^ 2 := by ring
    rw [hpow]
    calc ((2 ^ n) ^ 2) ^ 2 - 1 = ((2 ^ n) ^ 2) ^ 2 - 1 ^ 2 := by norm_num
      _ = ((2 ^ n) ^ 2 + 1) * ((2 ^ n) ^ 2 - 1) := Nat.sq_sub_sq _ _
      _ = ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 2 + 1) := by ring
  have h4fac : ((2 ^ n) ^ 4 - 1).factorization 3 = ((2 ^ n) ^ 2 - 1).factorization 3 := by
    rw [h4eq, Nat.factorization_mul h2m h2p, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h3q2p, add_zero]
  have hcard := card_hypSU_two_zero_nat h
  have hmain : (Nat.card (hypSU h 2 0)).factorization 3 =
      2 * ((2 ^ n) ^ 2 - 1).factorization 3 := by
    rw [hcard, Nat.factorization_mul (pow_ne_zero 6 hq0)
        (mul_ne_zero (mul_ne_zero h2m h3p) h4n),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd h3q6, zero_add,
      Nat.factorization_mul (mul_ne_zero h2m h3p) h4n, Finsupp.add_apply,
      Nat.factorization_mul h2m h3p, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h3q3, add_zero, h4fac]
    ring
  have hunits : Nat.card Kˣ = (2 ^ n) ^ 2 - 1 := by
    rw [Nat.card_units, h.card, show 2 * n = n * 2 by omega, pow_mul]
  rw [hmain, hunits]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3
