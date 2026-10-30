module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Zify
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Factors
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartTwo.Sec19

theorem exists_prime_gt_three_dvd_two_pow_sub_one {f : ℕ} (hf : 3 ≤ f) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2 ^ f - 1 := by
  by_contra hcon
  push Not at hcon
  have hpos : 0 < 2 ^ (f - 3) := by positivity
  have h8 : 2 ^ f = 8 * 2 ^ (f - 3) := by
    rw [show f = (f - 3) + 3 by omega, pow_add]
    simp [Nat.add_sub_cancel]; ring
  have hodd : ¬ 2 ∣ 2 ^ f - 1 := by omega
  have hne : 2 ^ f - 1 ≠ 0 := by omega
  have h3 : ∀ {d : ℕ}, d.Prime → d ∣ 2 ^ f - 1 → d = 3 := by
    intro d hd hdvd
    have hle : d ≤ 3 := by
      by_contra h
      exact hcon d hd (by omega) hdvd
    have h2 := hd.two_le
    interval_cases d
    · exact absurd hdvd hodd
    · rfl
  have heq := Nat.eq_prime_pow_of_unique_prime_dvd hne h3
  have hmod : ∀ a : ℕ, 3 ^ a % 8 = 1 ∨ 3 ^ a % 8 = 3 := by
    intro a
    induction a with
    | zero => simp
    | succ n ih => rw [pow_succ]; omega
  obtain ⟨a, ha⟩ : ∃ a : ℕ, 2 ^ f - 1 = 3 ^ a := ⟨_, heq⟩
  have hm := hmod a
  omega

theorem exists_prime_gt_three_dvd_two_pow_add_one {f : ℕ} (hf : f = 2 ∨ 4 ≤ f) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2 ^ f + 1 := by
  rcases hf with rfl | hf
  · exact ⟨5, by norm_num, by norm_num, by norm_num⟩
  by_contra hcon
  push Not at hcon
  have h16 : 2 ^ f = 16 * 2 ^ (f - 4) := by
    rw [show f = (f - 4) + 4 by omega, pow_add]
    simp [Nat.add_sub_cancel]; ring
  have hodd : ¬ 2 ∣ 2 ^ f + 1 := by omega
  have hne : 2 ^ f + 1 ≠ 0 := by omega
  have h3 : ∀ {d : ℕ}, d.Prime → d ∣ 2 ^ f + 1 → d = 3 := by
    intro d hd hdvd
    have hle : d ≤ 3 := by
      by_contra h
      exact hcon d hd (by omega) hdvd
    have h2 := hd.two_le
    interval_cases d
    · exact absurd hdvd hodd
    · rfl
  have heq := Nat.eq_prime_pow_of_unique_prime_dvd hne h3
  have hmod4 : ∀ n : ℕ, 3 ^ n % 16 = 1 → n % 4 = 0 := by
    intro n hn
    obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 4 ∧ n = 4 * k + r := ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
    have h81 : 81 ^ k % 16 = 1 := by rw [Nat.pow_mod]; norm_num
    have e : 3 ^ (4 * k + r) = 81 ^ k * 3 ^ r := by rw [pow_add, pow_mul]; norm_num
    rw [e, Nat.mul_mod, h81] at hn
    interval_cases r <;> simp_all
  obtain ⟨a, ha⟩ : ∃ a : ℕ, 2 ^ f + 1 = 3 ^ a := ⟨_, heq⟩
  have hmod16 : 3 ^ a % 16 = 1 := by omega
  have h4 : a % 4 = 0 := hmod4 a hmod16
  have h5 : 3 ^ a % 5 = 1 := by
    obtain ⟨b, rfl⟩ : 4 ∣ a := Nat.dvd_of_mod_eq_zero h4
    rw [pow_mul, Nat.pow_mod]; norm_num
  have h2f : 5 ∣ 2 ^ f := by omega
  have := (Nat.prime_five).dvd_of_dvd_pow h2f
  omega

theorem exists_prime_gt_three_dvd_sq_sub_one {f : ℕ} (hf : 2 ≤ f) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ (2 ^ f) ^ 2 - 1 := by
  rcases Nat.lt_or_ge f 3 with h | h
  · obtain rfl : f = 2 := by omega
    exact ⟨5, by norm_num, by norm_num, by norm_num⟩
  · obtain ⟨p, hp, hp3, hpd⟩ := exists_prime_gt_three_dvd_two_pow_sub_one h
    refine ⟨p, hp, hp3, hpd.trans ?_⟩
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have e : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      zify [h1, h2]; ring
    exact Dvd.intro _ e.symm

end CFSG.RankThree.PartTwo.Sec19
