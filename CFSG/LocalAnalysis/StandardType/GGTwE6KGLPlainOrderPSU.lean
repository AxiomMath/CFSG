module

public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.SCFourCover

private theorem two_pow_mod_six_plainOrd (k : ℕ) :
    2 ^ (2 * k + 1) % 6 = 2 ∧ 2 ^ (2 * k + 2) % 6 = 4 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e1 : 2 ^ (2 * (k + 1) + 1) = 2 ^ (2 * k + 1) * 4 := by ring
    have e2 : 2 ^ (2 * (k + 1) + 2) = 2 ^ (2 * k + 2) * 4 := by ring
    rw [e1, e2]
    omega

private theorem gcd_six_of_odd_plainOrd {m : ℕ} (hm : Odd m) : Nat.gcd 6 (2 ^ m + 1) = 3 := by
  obtain ⟨k, rfl⟩ := hm
  have h := (two_pow_mod_six_plainOrd k).1
  rw [Nat.gcd_rec 6 (2 ^ (2 * k + 1) + 1), show (2 ^ (2 * k + 1) + 1) % 6 = 3 by omega]
  norm_num

private theorem gcd_six_of_even_plainOrd {m : ℕ} (hm : Even m) (h0 : m ≠ 0) :
    Nat.gcd 6 (2 ^ m + 1) = 1 := by
  obtain ⟨k, rfl⟩ := hm
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := (two_pow_mod_six_plainOrd j).2
  rw [show j + 1 + (j + 1) = 2 * j + 2 by ring, Nat.gcd_rec 6 (2 ^ (2 * j + 2) + 1),
    show (2 ^ (2 * j + 2) + 1) % 6 = 5 by omega]
  norm_num

private theorem gcd_six_le_plainOrd {g n : ℕ} (hn : 1 ≤ n) (hgn : g ∣ n) :
    Nat.gcd 6 (2 ^ n + 1) ≤ Nat.gcd 6 (2 ^ g + 1) := by
  rcases Nat.even_or_odd n with he | ho
  · rw [gcd_six_of_even_plainOrd he (by omega)]
    exact Nat.gcd_pos_of_pos_left _ (by norm_num)
  · rw [gcd_six_of_odd_plainOrd ho, gcd_six_of_odd_plainOrd (Odd.of_dvd_nat ho hgn)]

private theorem toNat_factor_le_plainOrd {q q' : ℕ} (h : q ≤ q') (i : ℕ) :
    ((q : ℤ) ^ i - (-1) ^ i).toNat ≤ ((q' : ℤ) ^ i - (-1) ^ i).toNat := by
  have : (q : ℤ) ^ i ≤ (q' : ℤ) ^ i := pow_le_pow_left₀ (by positivity) (by exact_mod_cast h) i
  exact Int.toNat_le_toNat (by linarith)

theorem ordTwistedA_five_two_pow_le_of_dvd {g n : ℕ} (hn : 1 ≤ n) (hgn : g ∣ n) :
    CFSG.Open.ordTwistedA 5 (2 ^ g) ≤ CFSG.Open.ordTwistedA 5 (2 ^ n) := by
  have h : 2 ^ g ≤ 2 ^ n := Nat.pow_le_pow_right two_pos (Nat.le_of_dvd hn hgn)
  unfold CFSG.Open.ordTwistedA
  exact Nat.div_le_div (Nat.mul_le_mul (Nat.pow_le_pow_left h _)
    (Finset.prod_le_prod' fun i _ => toNat_factor_le_plainOrd h i)) (gcd_six_le_plainOrd hn hgn)
    (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'

private theorem pow_le_toNat_factor_plainOrd {q i : ℕ} (hq : 2 ≤ q) (hi : 1 ≤ i) :
    q ^ (i - 1 + i % 2) ≤ ((q : ℤ) ^ i - (-1) ^ i).toNat := by
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  rcases Nat.even_or_odd i with he | ho
  · rw [Nat.even_iff.1 he, add_zero, he.neg_one_pow]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have h1 : (1 : ℤ) ≤ (q : ℤ) ^ j := one_le_pow₀ (by linarith)
    have h2 : (q : ℤ) ^ j * 2 ≤ (q : ℤ) ^ j * q := mul_le_mul_of_nonneg_left hq' (by positivity)
    refine (Int.toNat_natCast (q ^ j)).symm.le.trans (Int.toNat_le_toNat ?_)
    push_cast
    rw [pow_succ]
    linarith
  · rw [Nat.odd_iff.1 ho, ho.neg_one_pow, Nat.sub_add_cancel hi]
    refine (Int.toNat_natCast (q ^ i)).symm.le.trans (Int.toNat_le_toNat ?_)
    push_cast
    linarith

theorem pow_twentyNine_lt_ordTwistedA_five {g : ℕ} (hg : 1 ≤ g) :
    (2 ^ g) ^ 29 < CFSG.Open.ordTwistedA 5 (2 ^ g) := by
  have hq : 2 ≤ 2 ^ g := Nat.one_lt_two_pow (by omega)
  have hprod : (2 ^ g) ^ 17 ≤
      ∏ i ∈ Finset.Icc 2 (5 + 1), (((2 ^ g : ℕ) : ℤ) ^ i - (-1) ^ i).toNat := by
    calc (2 ^ g) ^ 17 = ∏ i ∈ Finset.Icc 2 (5 + 1), (2 ^ g) ^ (i - 1 + i % 2) := by
          rw [Finset.prod_pow_eq_pow_sum,
            show ∑ i ∈ Finset.Icc 2 (5 + 1), (i - 1 + i % 2) = 17 by decide]
      _ ≤ _ := Finset.prod_le_prod' fun i hi =>
          pow_le_toNat_factor_plainOrd hq (by simp only [Finset.mem_Icc] at hi; omega)
  have hgcd : Nat.gcd (5 + 1) (2 ^ g + 1) ≤ 3 := by
    show Nat.gcd 6 (2 ^ g + 1) ≤ 3
    rcases Nat.even_or_odd g with he | ho
    · rw [gcd_six_of_even_plainOrd he (by omega)]
      norm_num
    · rw [gcd_six_of_odd_plainOrd ho]
  have h4 : 4 ≤ (2 ^ g) ^ 2 := by nlinarith
  refine lt_of_lt_of_le (Nat.pow_lt_pow_right hq (by norm_num : 29 < 30)) ?_
  unfold CFSG.Open.ordTwistedA
  rw [Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_left _ (by norm_num))]
  calc (2 ^ g) ^ 30 * Nat.gcd (5 + 1) (2 ^ g + 1) ≤ (2 ^ g) ^ 30 * (2 ^ g) ^ 2 :=
        Nat.mul_le_mul_left _ (by omega)
    _ = (2 ^ g) ^ (5 * (5 + 1) / 2) * (2 ^ g) ^ 17 := by rw [← pow_add, ← pow_add]
    _ ≤ _ := Nat.mul_le_mul_left _ hprod

end CFSG.StandardType.SCFourCover
