module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem gffa2_two_pow_two_mul_mod_three (m : ℕ) : 2 ^ (2 * m) % 3 = 1 := by
  rw [pow_mul, Nat.pow_mod]
  norm_num

private theorem gffa2_two_pow_two_mul_add_one_mod_three (m : ℕ) :
    2 ^ (2 * m + 1) % 3 = 2 := by
  rw [pow_succ, Nat.mul_mod, gffa2_two_pow_two_mul_mod_three]

private theorem gffa2_two_pow_mod_three_eq_one_iff (n : ℕ) : 2 ^ n % 3 = 1 ↔ Even n := by
  constructor
  · intro h
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · exact ⟨k, by omega⟩
    · rw [hk, gffa2_two_pow_two_mul_add_one_mod_three] at h
      exfalso
      omega
  · rintro ⟨k, rfl⟩
    rw [← two_mul]
    exact gffa2_two_pow_two_mul_mod_three k

private theorem gffa2_two_pow_mod_three_eq_two_iff (n : ℕ) : 2 ^ n % 3 = 2 ↔ Odd n := by
  constructor
  · intro h
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · rw [hk, gffa2_two_pow_two_mul_mod_three] at h
      exfalso
      omega
    · exact ⟨k, by omega⟩
  · rintro ⟨k, rfl⟩
    exact gffa2_two_pow_two_mul_add_one_mod_three k

private theorem gffa2_three_dvd_sub_one_iff_mod (n : ℕ) :
    3 ∣ 2 ^ n - 1 ↔ 2 ^ n % 3 = 1 := by
  constructor
  · intro hd
    obtain ⟨r, hr⟩ := hd
    have hle : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h1 : 2 ^ n = 3 * r + 1 := by omega
    rw [h1, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by norm_num : 1 < 3)]
  · intro hmod
    refine ⟨2 ^ n / 3, ?_⟩
    have hdiv := Nat.div_add_mod (2 ^ n) 3
    omega

private theorem gffa2_three_dvd_add_one_iff_mod (n : ℕ) :
    3 ∣ 2 ^ n + 1 ↔ 2 ^ n % 3 = 2 := by
  constructor
  · intro hd
    obtain ⟨r, hr⟩ := hd
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · exfalso
        rw [h0, mul_zero] at hr
        exact Nat.succ_ne_zero (2 ^ n) hr
      · exact hpos
    have h1 : 2 ^ n = 3 * (r - 1) + 2 := by omega
    rw [h1, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by norm_num : 2 < 3)]
  · intro hmod
    refine ⟨2 ^ n / 3 + 1, ?_⟩
    have hdiv := Nat.div_add_mod (2 ^ n) 3
    omega

theorem gffa2_three_dvd_pow_sub_one_iff (n : ℕ) : 3 ∣ 2 ^ n - 1 ↔ Even n := by
  rw [gffa2_three_dvd_sub_one_iff_mod n]
  exact gffa2_two_pow_mod_three_eq_one_iff n

theorem gffa2_three_dvd_pow_add_one_iff (n : ℕ) : 3 ∣ 2 ^ n + 1 ↔ Odd n := by
  rw [gffa2_three_dvd_add_one_iff_mod n]
  exact gffa2_two_pow_mod_three_eq_two_iff n

theorem gffa2_even_of_linear {n m : ℕ} (h3 : 3 ∣ 2 ^ n - 1) (hm : n = 3 * m) :
    Even m := by
  have hn : Even n := (gffa2_three_dvd_pow_sub_one_iff n).mp h3
  obtain ⟨k, hk⟩ := hn
  rw [hk] at hm
  have h2 : 2 ∣ 3 * m := ⟨k, by omega⟩
  exact even_iff_two_dvd.mpr (Nat.Coprime.dvd_of_dvd_mul_left (by decide) h2)

theorem gffa2_odd_of_unitary {n m : ℕ} (h3 : 3 ∣ 2 ^ n + 1) (hm : n = 3 * m) :
    Odd m := by
  have hn : Odd n := (gffa2_three_dvd_pow_add_one_iff n).mp h3
  obtain ⟨k, hk⟩ := hn
  rw [hk] at hm
  have hodd : Odd (3 * m) := ⟨k, by omega⟩
  exact (Nat.odd_mul.mp hodd).2

theorem gffa2_label_linear {m : ℕ} (hm : Even m) (hm1 : 1 ≤ m) :
    LargeEvenInLambda2 ⟨.A, 2, m⟩ ∧ GGLabelA2 ⟨.A, 2, m⟩ := by
  have hm2 : 2 ≤ m := by
    obtain ⟨k, hk⟩ := hm
    omega
  have hdvd : 3 ∣ 2 ^ m - 1 := (gffa2_three_dvd_pow_sub_one_iff m).mpr hm
  refine ⟨⟨hm1, by norm_num, by intro h; omega⟩, rfl, hm2, Or.inl ⟨rfl, hdvd⟩⟩

theorem gffa2_label_unitary {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    LargeEvenInLambda2 ⟨.twA, 2, m⟩ ∧ GGLabelA2 ⟨.twA, 2, m⟩ := by
  have hm2 : 2 ≤ m := by omega
  have hdvd : 3 ∣ 2 ^ m + 1 := (gffa2_three_dvd_pow_add_one_iff m).mpr hm
  refine ⟨⟨le_trans (by norm_num : 1 ≤ 3) hm3, by norm_num, by intro h; omega⟩, rfl, hm2,
    Or.inr ⟨rfl, hdvd⟩⟩

end CFSG.StandardType
