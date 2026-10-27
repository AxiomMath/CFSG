module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.Quasithin.Background.P3G2Zorn

public section

namespace CFSG.Quasithin.H13.NQCat.NGT

open CFSG.Assembly.LowTwoRank

section Arith

@[expose] def sl2Form (a : ℕ) : ℕ := 2 ^ a * (2 ^ (2 * a) - 1)

@[expose] def sl3Form (a : ℕ) : ℕ := 2 ^ (3 * a) * ((2 ^ (2 * a) - 1) * (2 ^ (3 * a) - 1))

@[expose] def sp4Form (a : ℕ) : ℕ := 2 ^ (4 * a) * ((2 ^ (2 * a) - 1) * (2 ^ (4 * a) - 1))

@[expose] def g2Form (a : ℕ) : ℕ := 2 ^ (6 * a) * ((2 ^ (6 * a) - 1) * (2 ^ (2 * a) - 1))

theorem odd_two_pow_sub_one {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m - 1) := by
  have h : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨k, hk⟩ : Even (2 ^ m) := Nat.even_pow.2 ⟨even_two, by omega⟩
  exact ⟨k - 1, by omega⟩

theorem two_pow_mul_odd_inj {k l u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ k * u = 2 ^ l * v) : k = l ∧ u = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hu) (Nat.even_iff.2 rfl)
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hv) (Nat.even_iff.2 rfl)
  have hu2 : ¬ 2 ∣ u := by
    obtain ⟨m, rfl⟩ := hu
    omega
  have hv2 : ¬ 2 ∣ v := by
    obtain ⟨m, rfl⟩ := hv
    omega
  have h1 := congrArg (padicValNat 2) h
  rw [padicValNat.mul (by positivity) hu0, padicValNat.mul (by positivity) hv0,
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hu2,
    padicValNat.eq_zero_of_not_dvd hv2] at h1
  simp only [add_zero] at h1
  subst h1
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

theorem odd_mul_odd_parts {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Odd ((2 ^ a - 1) * (2 ^ b - 1)) :=
  (odd_two_pow_sub_one ha).mul (odd_two_pow_sub_one hb)

theorem two_pow_inj {a b : ℕ} (h : 2 ^ a = 2 ^ b) : a = b :=
  Nat.pow_right_injective (le_refl 2) h

theorem two_pow_sub_one_inj {a b : ℕ} (h : 2 ^ a - 1 = 2 ^ b - 1) : a = b := by
  have ha := Nat.one_le_two_pow (n := a)
  have hb := Nat.one_le_two_pow (n := b)
  exact two_pow_inj (by omega)

theorem sl3Form_ne_sl2Form {a n : ℕ} (ha : 1 ≤ a) (hn : 1 ≤ n) : sl3Form n ≠ sl2Form a := by
  intro h
  obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj (odd_mul_odd_parts (by omega) (by omega))
    (odd_two_pow_sub_one (by omega)) h
  subst h1
  have hx : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set x := 2 ^ n with hxdef
  have e2 : 2 ^ (2 * n) = x ^ 2 := by rw [hxdef, ← pow_mul, mul_comm]
  have e3 : 2 ^ (3 * n) = x ^ 3 := by rw [hxdef, ← pow_mul, mul_comm]
  have e6 : 2 ^ (2 * (3 * n)) = x ^ 6 := by rw [hxdef, ← pow_mul]; ring_nf
  rw [e2, e3, e6] at h2
  have h21 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h31 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h61 : 1 ≤ x ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h21, h31, h61] at h2
  nlinarith [h2, hx]

theorem sp4Form_ne_sl2Form {a n : ℕ} (ha : 1 ≤ a) (hn : 1 ≤ n) : sp4Form n ≠ sl2Form a := by
  intro h
  obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj (odd_mul_odd_parts (by omega) (by omega))
    (odd_two_pow_sub_one (by omega)) h
  subst h1
  have hx : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set x := 2 ^ n with hxdef
  have e2 : 2 ^ (2 * n) = x ^ 2 := by rw [hxdef, ← pow_mul, mul_comm]
  have e4 : 2 ^ (4 * n) = x ^ 4 := by rw [hxdef, ← pow_mul, mul_comm]
  have e8 : 2 ^ (2 * (4 * n)) = x ^ 8 := by rw [hxdef, ← pow_mul]; ring_nf
  rw [e2, e4, e8] at h2
  have h21 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h41 : 1 ≤ x ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h81 : 1 ≤ x ^ 8 := Nat.one_le_pow _ _ (by omega)
  zify [h21, h41, h81] at h2
  nlinarith [h2, hx]

theorem sl3Form_ne_g2Form {a n : ℕ} (ha : 1 ≤ a) (hn : 1 ≤ n) : sl3Form n ≠ g2Form a := by
  intro h
  obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj (odd_mul_odd_parts (by omega) (by omega))
    (odd_mul_odd_parts (by omega) (by omega)) h
  rw [h1, mul_comm (2 ^ (6 * a) - 1)] at h2
  have hpos : 0 < 2 ^ (6 * a) - 1 := by
    have := Nat.one_lt_two_pow (n := 6 * a) (by omega)
    omega
  have h3 := Nat.eq_of_mul_eq_mul_right hpos h2
  have := two_pow_sub_one_inj h3
  omega

theorem sp4Form_ne_g2Form {a n : ℕ} (ha : 1 ≤ a) (hn : 1 ≤ n) : sp4Form n ≠ g2Form a := by
  intro h
  obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj (odd_mul_odd_parts (by omega) (by omega))
    (odd_mul_odd_parts (by omega) (by omega)) h
  rw [h1, mul_comm (2 ^ (6 * a) - 1)] at h2
  have hpos : 0 < 2 ^ (6 * a) - 1 := by
    have := Nat.one_lt_two_pow (n := 6 * a) (by omega)
    omega
  have h3 := Nat.eq_of_mul_eq_mul_right hpos h2
  have := two_pow_sub_one_inj h3
  omega

theorem sl3Form_ge {n : ℕ} (hn : 2 ≤ n) : 60480 ≤ sl3Form n := by
  have h1 : 2 ^ (3 * 2) ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (2 * 2) ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold sl3Form
  calc 60480 = 2 ^ (3 * 2) * ((2 ^ (2 * 2) - 1) * (2 ^ (3 * 2) - 1)) := by norm_num
    _ ≤ 2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1)) := by
      gcongr

theorem sp4Form_ge {n : ℕ} (hn : 2 ≤ n) : 979200 ≤ sp4Form n := by
  have h1 : 2 ^ (4 * 2) ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (2 * 2) ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold sp4Form
  calc 979200 = 2 ^ (4 * 2) * ((2 ^ (2 * 2) - 1) * (2 ^ (4 * 2) - 1)) := by norm_num
    _ ≤ 2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) := by
      gcongr

theorem sl3Form_ne_l5 (n : ℕ) : sl3Form n ≠ 9999360 := by
  intro h
  have h9 : (9999360 : ℕ) = 2 ^ 10 * 9765 := by norm_num
  rw [h9] at h
  rcases Nat.lt_or_ge n 1 with hn | hn
  · interval_cases n
    norm_num [sl3Form] at h
  · obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj (odd_mul_odd_parts (by omega) (by omega))
      ⟨4882, by norm_num⟩ h
    omega

theorem sp4Form_ne_l5 (n : ℕ) : sp4Form n ≠ 9999360 := by
  intro h
  have h9 : (9999360 : ℕ) = 2 ^ 10 * 9765 := by norm_num
  rw [h9] at h
  rcases Nat.lt_or_ge n 1 with hn | hn
  · interval_cases n
    norm_num [sp4Form] at h
  · obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj (odd_mul_odd_parts (by omega) (by omega))
      ⟨4882, by norm_num⟩ h
    omega

end Arith

section Card

variable {K : Type} [Field K] [Finite K] {a : ℕ}

theorem card_sl2_form (hK : Nat.card K = 2 ^ a) : Nat.card ↥(StatedSL 2 K) = sl2Form a := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hK, sl2Form]
  simp [← pow_mul, mul_comm]

theorem card_sl3_form (hK : Nat.card K = 2 ^ a) : Nat.card ↥(StatedSL 3 K) = sl3Form a := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hK, sl3Form]
  have hI : Finset.Icc 2 3 = {2, 3} := by decide
  rw [hI, Finset.prod_pair (by norm_num)]
  simp [← pow_mul, mul_comm]

theorem card_sp4_form (hK : Nat.card K = 2 ^ a) : Nat.card ↥(StatedSp 2 K) = sp4Form a := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK, sp4Form]
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)]
  simp [← pow_mul, mul_comm]

theorem card_g2_form [CharP K 2] (hK : Nat.card K = 2 ^ a) :
    Nat.card ↥(CFSG.Open.quasithinG2 K) = g2Form a := by
  rw [CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup,
    CFSG.Quasithin.Vol2.KGNat.card_cayleyGroup, hK, g2Form]
  simp [← pow_mul, mul_comm]

end Card

end CFSG.Quasithin.H13.NQCat.NGT
