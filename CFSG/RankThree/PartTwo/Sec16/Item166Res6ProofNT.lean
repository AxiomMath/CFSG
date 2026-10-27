module

public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Res6

theorem exists_three_pow_mul_card_SL {q : ℕ} (hq : q % 3 = 1) (hq2 : 2 ≤ q) :
    ∃ c, ¬ 3 ∣ c ∧
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) = 3 ^ (2 * (q - 1).factorization 3 + 1) * c := by
  set a := (q - 1).factorization 3 with ha
  have hq0 : q - 1 ≠ 0 := by omega
  have hqm : 3 ^ a * ((q - 1) / 3 ^ a) = q - 1 := Nat.ordProj_mul_ordCompl_eq_self (q - 1) 3
  set m := (q - 1) / 3 ^ a with hm
  have hm3 : ¬ 3 ∣ m := Nat.not_dvd_ordCompl Nat.prime_three hq0
  have ha1 : 1 ≤ a := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hq0).mp (by omega)
  obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  set t := 3 ^ b * m with ht
  have hqt : q = 3 * t + 1 := by
    have : 3 ^ a * m = 3 * t := by rw [hb, ht, pow_succ]; ring
    omega
  have h2 : q ^ 2 - 1 = 3 * t * (3 * t + 2) := by
    rw [hqt, show (3 * t + 1) ^ 2 = 3 * t * (3 * t + 2) + 1 by ring, Nat.add_sub_cancel]
  have h3 : q ^ 3 - 1 = 9 * t * (3 * t ^ 2 + 3 * t + 1) := by
    rw [hqt, show (3 * t + 1) ^ 3 = 9 * t * (3 * t ^ 2 + 3 * t + 1) + 1 by ring,
      Nat.add_sub_cancel]
  refine ⟨m ^ 2 * (q ^ 3 * ((3 * t + 2) * (3 * t ^ 2 + 3 * t + 1))), ?_, ?_⟩
  · intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h | h
    · exact hm3 (Nat.prime_three.dvd_of_dvd_pow h)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · omega
    · have : 3 * t ^ 2 + 3 * t + 1 = 3 * (t ^ 2 + t) + 1 := by ring
      omega
  · rw [h2, h3, hb, ht]
    ring

theorem factorization_sq_sub_one_three {q : ℕ} (hq : q % 3 = 2) :
    (q ^ 2 - 1).factorization 3 = (q + 1).factorization 3 := by
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    rw [show (r + 1) ^ 2 = (r + 1 - 1) * (r + 1 + 1) + 1 by
      rw [Nat.add_sub_cancel]; ring, Nat.add_sub_cancel]
  rw [hsq, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by omega), zero_add]

theorem exists_three_pow_mul_card_SU {q : ℕ} (hq : q % 3 = 2) :
    ∃ c, ¬ 3 ∣ c ∧
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) = 3 ^ (2 * (q ^ 2 - 1).factorization 3 + 1) * c := by
  rw [factorization_sq_sub_one_three hq]
  set a := (q + 1).factorization 3 with ha
  have hq0 : q + 1 ≠ 0 := by omega
  have hqm : 3 ^ a * ((q + 1) / 3 ^ a) = q + 1 := Nat.ordProj_mul_ordCompl_eq_self (q + 1) 3
  set m := (q + 1) / 3 ^ a with hm
  have hm3 : ¬ 3 ∣ m := Nat.not_dvd_ordCompl Nat.prime_three hq0
  have ha1 : 1 ≤ a := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hq0).mp (by omega)
  obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hm0 : m ≠ 0 := fun h0 => by rw [h0, mul_zero] at hqm; omega
  set s := 3 ^ b * m with hs
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num)) hm0)
  obtain ⟨t, ht⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hqt : q = 3 * t + 2 := by
    have : 3 ^ a * m = 3 * s := by rw [hb, hs, pow_succ]; ring
    omega
  have h2 : q ^ 2 - 1 = 3 * (t + 1) * (3 * t + 1) := by
    rw [hqt, show (3 * t + 2) ^ 2 = 3 * (t + 1) * (3 * t + 1) + 1 by ring, Nat.add_sub_cancel]
  have h3 : q ^ 3 + 1 = 9 * (t + 1) * (3 * t ^ 2 + 3 * t + 1) := by
    rw [hqt]
    ring
  refine ⟨m ^ 2 * (q ^ 3 * ((3 * t + 1) * (3 * t ^ 2 + 3 * t + 1))), ?_, ?_⟩
  · intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h | h
    · exact hm3 (Nat.prime_three.dvd_of_dvd_pow h)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · omega
    · have : 3 * t ^ 2 + 3 * t + 1 = 3 * (t ^ 2 + t) + 1 := by ring
      omega
  · rw [h2, h3, hb, ← ht, hs]
    ring

end CFSG.RankThree.PartTwo.Sec16.Proof166Res6
