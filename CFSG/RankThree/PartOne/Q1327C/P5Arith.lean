module

public import CFSG.Open.Defs

public section

namespace CFSG.RankThree.PartOne.Q1327C

theorem mod_four_of_dvd_five {f : ℕ} (h : 5 ∣ 2 ^ f + 1) : f % 4 = 2 := by
  have h1 : (2 ^ f + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h
  have h2 : 2 ^ f % 5 = 2 ^ (f % 4) % 5 := by
    conv_lhs => rw [← Nat.div_add_mod f 4, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have : f % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : f % 4 <;> omega

theorem thirteen_dvd_of_mod_four {f : ℕ} (h : f % 4 = 2) : 13 ∣ (2 ^ f) ^ 3 + 1 := by
  have h1 : (2 ^ f) ^ 3 = 2 ^ (12 * (f / 4) + 6) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [h1, pow_add, pow_mul]
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem ordTwistedA_two_mul (q : ℕ) (hq : 2 ≤ q) :
    CFSG.Open.ordTwistedA 2 q * Nat.gcd 3 (q + 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  unfold CFSG.Open.ordTwistedA
  have h1 : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  rw [h1, Finset.prod_pair (by norm_num)]
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e2 : (((q : ℤ)) ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
    have : (((q : ℤ)) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hq2]
      ring
    rw [this, Int.toNat_natCast]
  have e3 : (((q : ℤ)) ^ 3 - (-1 : ℤ) ^ 3).toNat = q ^ 3 + 1 := by
    have : (((q : ℤ)) ^ 3 - (-1 : ℤ) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [this, Int.toNat_natCast]
  rw [e2, e3]
  have h3 : Nat.gcd 3 (q + 1) ∣ q + 1 := Nat.gcd_dvd_right _ _
  have h4 : (q + 1) ∣ q ^ 2 - 1 := by
    refine ⟨q - 1, ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ q)
    simp only [Nat.add_sub_cancel_left]
    have : (1 + k) ^ 2 = (1 + k + 1) * k + 1 := by ring
    omega
  have hdvd : Nat.gcd 3 (q + 1) ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
    ((h3.trans h4).mul_right (q ^ 3 + 1)).mul_left (q ^ 3)
  have e4 : 2 * (2 + 1) / 2 = 3 := by norm_num
  rw [e4]
  exact Nat.div_mul_cancel hdvd

theorem prime_dvd_ordTwistedA_two {q r : ℕ} (hq : 2 ≤ q) (hr : r.Prime) (h3 : 3 < r)
    (h : r ∣ q ^ 3 + 1) : r ∣ CFSG.Open.ordTwistedA 2 q := by
  have hmul := ordTwistedA_two_mul q hq
  have hdvd : r ∣ CFSG.Open.ordTwistedA 2 q * Nat.gcd 3 (q + 1) := by
    rw [hmul]
    exact (h.mul_left _).mul_left _
  rcases hr.dvd_mul.1 hdvd with h' | h'
  · exact h'
  · exfalso
    have hle : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by norm_num)) h'
    omega

theorem thirteen_dvd_ordTwistedA_two {f : ℕ} (hf : 1 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) :
    13 ∣ CFSG.Open.ordTwistedA 2 (2 ^ f) := by
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact prime_dvd_ordTwistedA_two hq (by norm_num) (by norm_num)
    (thirteen_dvd_of_mod_four (mod_four_of_dvd_five h5))

theorem five_dvd_ordTwistedA_two {f : ℕ} (hf : 1 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) :
    5 ∣ CFSG.Open.ordTwistedA 2 (2 ^ f) := by
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine prime_dvd_ordTwistedA_two hq (by norm_num) (by norm_num) (h5.trans ?_)
  simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ f) 1 (by decide : Odd 3)

theorem not_prime_ordTwistedA_two {f : ℕ} (hf : 1 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) :
    ¬ (CFSG.Open.ordTwistedA 2 (2 ^ f)).Prime := by
  intro hp
  have h1 := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 (five_dvd_ordTwistedA_two hf h5)
  have h2 := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 (thirteen_dvd_ordTwistedA_two hf h5)
  omega

end CFSG.RankThree.PartOne.Q1327C
