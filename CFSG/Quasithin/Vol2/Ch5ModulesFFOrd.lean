module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13

open CFSG.Assembly.LowTwoRank

theorem two_pow_mul_odd_inj {a b x y : ℕ} (hx : Odd x) (hy : Odd y)
    (h : 2 ^ a * x = 2 ^ b * y) : a = b ∧ x = y := by
  have key : ∀ {a b x y : ℕ}, Odd x → 2 ^ a * x = 2 ^ b * y → a < b → False := by
    intro a b x y hx h hab
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have h1 : 2 ^ a * x = 2 ^ a * (2 ^ (k + 1) * y) := by
      rw [h, pow_add, pow_add, pow_add]
      ring
    have h2 : x = 2 ^ (k + 1) * y := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    have h3 : Even x := by
      rw [h2, pow_succ]
      exact ⟨2 ^ k * y, by ring⟩
    exact (Nat.not_even_iff_odd.mpr hx) h3
  rcases Nat.lt_trichotomy a b with hab | rfl | hab
  · exact (key hx h hab).elim
  · exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩
  · exact (key hy h.symm hab).elim

theorem odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have he : Even (2 ^ k) := (Nat.even_pow' (by omega)).mpr even_two
  exact Nat.Even.sub_odd h1 he odd_one

theorem odd_two_pow_pow_sub_one {m j : ℕ} (hm : 1 ≤ m) (hj : 1 ≤ j) : Odd ((2 ^ m) ^ j - 1) := by
  rw [← pow_mul]
  exact odd_two_pow_sub_one (Nat.one_le_iff_ne_zero.mpr (by positivity))

theorem l2Order_lt_succ (n : ℕ) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) < 2 ^ (n + 1) * ((2 ^ (n + 1)) ^ 2 - 1) := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ (2 ^ (n + 1)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have e : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, mul_comm]
  rw [e] at h3 ⊢
  zify [h2, h3]
  nlinarith

theorem l2Order_strictMono : StrictMono fun n : ℕ => 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
  strictMono_nat_of_lt_succ l2Order_lt_succ

theorem l2Order_inj {m n : ℕ} (h : 2 ^ m * ((2 ^ m) ^ 2 - 1) = 2 ^ n * ((2 ^ n) ^ 2 - 1)) :
    m = n :=
  l2Order_strictMono.injective h

theorem le_seven_of_l2Order_lt {n c : ℕ} (h : 2 ^ n * ((2 ^ n) ^ 2 - 1) = c)
    (hc : c < 16776960) : n ≤ 7 := by
  by_contra hn
  have h8 : 2 ^ 8 * ((2 ^ 8) ^ 2 - 1) ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
    l2Order_strictMono.monotone (by omega)
  norm_num at h8
  omega

theorem l2Order_ne_sl3 {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1) ≠ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  intro h
  have hodd : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) :=
    (odd_two_pow_pow_sub_one hm (by norm_num)).mul (odd_two_pow_pow_sub_one hm (by norm_num))
  have h' : 2 ^ (3 * m) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [← h, mul_comm 3 m, pow_mul, mul_assoc]
  obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj hodd (odd_two_pow_pow_sub_one hn (by norm_num)) h'
  rw [← h1, mul_comm 3 m, pow_mul] at h2
  set q := 2 ^ m with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have e1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e2 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have e3 : 1 ≤ (q ^ 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [e1, e2, e3] at h2
  nlinarith [h2]

theorem l2Order_ne_sp4 {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (2 ^ m) ^ (2 ^ 2) * ∏ j ∈ Finset.Icc 1 2, ((2 ^ m) ^ (2 * j) - 1) ≠
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  intro h
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)] at h
  norm_num at h
  have hodd : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) :=
    (odd_two_pow_pow_sub_one hm (by norm_num)).mul (odd_two_pow_pow_sub_one hm (by norm_num))
  have h' : 2 ^ (4 * m) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [← h, mul_comm 4 m, pow_mul]
  obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj hodd (odd_two_pow_pow_sub_one hn (by norm_num)) h'
  rw [← h1, mul_comm 4 m, pow_mul] at h2
  set q := 2 ^ m with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have e1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e2 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have e3 : 1 ≤ (q ^ 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [e1, e2, e3] at h2
  nlinarith [h2]

theorem card_statedSL_two {K : Type} [Field K] [Finite K] :
    Nat.card (StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two K

theorem card_statedSL_three_zmodTwo : Nat.card (StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

theorem card_statedSL_four_zmodTwo : Nat.card (StatedSL 4 (ZMod 2)) = 20160 :=
  CFSG.Open.StatedAPI.card_statedSL_four_zmod_two

theorem card_statedSL_five_zmodTwo : Nat.card (StatedSL 5 (ZMod 2)) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_zmod_two

end CFSG.Quasithin.H13
