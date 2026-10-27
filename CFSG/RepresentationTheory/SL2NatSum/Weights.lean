module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

public section

namespace CFSG.RepresentationTheory.SL2NatSum

local notation "Z" n => ZMod (2 ^ n - 1)

@[expose] def IsTorusWt (n : ℕ) (a : ZMod (2 ^ n - 1)) : Prop := ∃ i : ℕ, a = 2 ^ i ∨ a = -2 ^ i

private lemma two_pow_eq_two_mul {n : ℕ} (hn : 1 ≤ n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  conv_lhs => rw [← Nat.sub_add_cancel hn]
  rw [pow_succ, mul_comm]

private lemma pow_eq_one_zmod {n : ℕ} (hn : 1 ≤ n) : (2 : Z n) ^ n = 1 := by
  change (((2 : ℕ) : Z n) ^ n) = 1
  rw [← Nat.cast_pow]
  have h : 2 ^ n = (2 ^ n - 1) + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  rw [h, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]

private lemma pow_eq_pow_mod_zmod {n i : ℕ} (hn : 1 ≤ n) :
    (2 : Z n) ^ i = (2 : Z n) ^ (i % n) := pow_eq_pow_mod i (pow_eq_one_zmod hn)

private lemma isUnit_two_zmod {n : ℕ} (hn : 1 ≤ n) : IsUnit (2 : Z n) := by
  have hodd : Odd (2 ^ n - 1) := Nat.Even.sub_odd Nat.one_le_two_pow
    (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two (by omega)) odd_one
  exact (ZMod.isUnit_iff_coprime 2 (2 ^ n - 1)).mpr (Nat.coprime_two_left.mpr hodd)

private lemma pow_lt_N {n l : ℕ} (hn : 2 ≤ n) (hl : l < n) : 2 ^ l < 2 ^ n - 1 := by
  have hle : 2 ^ l ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmul : 2 ^ n = 2 * 2 ^ (n - 1) := two_pow_eq_two_mul (by omega)
  have hge : 2 ≤ 2 ^ (n - 1) := by
    have := Nat.one_lt_two_pow (by omega : n - 1 ≠ 0)
    omega
  omega

private lemma one_add_pow_lt_N {n l : ℕ} (hn : 3 ≤ n) (hl : l < n) :
    1 + 2 ^ l < 2 ^ n - 1 := by
  have hle : 2 ^ l ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmul : 2 ^ n = 2 * 2 ^ (n - 1) := two_pow_eq_two_mul (by omega)
  have hge : 2 < 2 ^ (n - 1) := by
    have h4 : 2 ^ 2 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h4
    omega
  omega

private lemma natCast_inj_of_lt {N a b : ℕ} (ha : a < N) (hb : b < N)
    (h : (a : ZMod N) = (b : ZMod N)) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at this

private lemma natCast_sum_eq_zero {n s : ℕ} (hpos : 0 < s)
    (hlt : s < 2 * (2 ^ n - 1)) (h : (s : Z n) = 0) : s = 2 ^ n - 1 := by
  have hdvd : (2 ^ n - 1) ∣ s := (ZMod.natCast_eq_zero_iff s (2 ^ n - 1)).mp h
  exact Nat.eq_of_dvd_of_lt_two_mul hpos.ne' hdvd hlt

private lemma two_add_pow_add_pow_ne {n l m : ℕ} (hn : 4 ≤ n)
    (hl : l < n) (hm : m < n) (h : 2 + 2 ^ l + 2 ^ m = 2 ^ n) : False := by
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := two_pow_eq_two_mul (by omega)
  have hpow' : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    simpa [show n - 1 - 1 = n - 2 by omega] using two_pow_eq_two_mul (n := n - 1) (by omega)
  have h4 : 4 ≤ 2 ^ (n - 2) := by
    simpa using Nat.pow_le_pow_right (n := 2) (by norm_num) (show 2 ≤ n - 2 by omega)
  wlog hlm : l ≤ m generalizing l m
  · have h' : 2 + 2 ^ m + 2 ^ l = 2 ^ n := by omega
    exact this hm hl h' (le_of_not_ge hlm)
  by_cases hm2 : m ≤ n - 2
  · have h1 : 2 ^ l ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ m ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  · have hm_eq : m = n - 1 := by omega
    subst hm_eq
    by_cases hl2 : l ≤ n - 2
    · have h1 : 2 ^ l ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) hl2
      omega
    · have hl_eq : l = n - 1 := by omega
      subst hl_eq
      omega

private lemma pow_eq_pow_add_one_imp {n l m : ℕ} (hn : 4 ≤ n) (hl : l < n)
    (hm : m < n) (h : 2 ^ l = 2 ^ m + 1) : l = 1 := by
  by_cases hl0 : l = 0
  · subst hl0; have := Nat.two_pow_pos m; omega
  · by_cases hm0 : m = 0
    · subst hm0
      exact Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) (by simpa using h)
    · have he : Even (2 ^ l) := Even.pow_of_ne_zero (a := (2 : ℕ)) even_two (by omega)
      have ho : Odd (2 ^ m + 1) :=
        (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two hm0).add_one
      exact False.elim ((Nat.not_even_iff_odd.mpr ho) (by rwa [← h]))

private lemma pow_add_pow_eq_two_pow_imp {n l m : ℕ} (hn : 4 ≤ n)
    (hl : l < n) (hm : m < n) (h : 2 ^ l + 2 ^ m = 2 ^ n) : l = n - 1 := by
  have hmul : 2 ^ n = 2 * 2 ^ (n - 1) := two_pow_eq_two_mul (by omega)
  have h1 : 2 ^ l ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ m ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have heq : 2 ^ l = 2 ^ (n - 1) := by omega
  exact Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) (by simpa using heq)

private lemma isTorusWt_iff {n : ℕ} (hn : 1 ≤ n) (a : Z n) : IsTorusWt n a ↔
    ∃ l : ℕ, l < n ∧ (a = (2 : Z n) ^ l ∨ a = -(2 : Z n) ^ l) := by
  constructor
  · rintro ⟨i, rfl | rfl⟩
    · exact ⟨i % n, Nat.mod_lt i (by omega), Or.inl (pow_eq_pow_mod_zmod hn)⟩
    · exact ⟨i % n, Nat.mod_lt i (by omega), Or.inr (by rw [pow_eq_pow_mod_zmod hn])⟩
  · rintro ⟨l, -, rfl | rfl⟩
    · exact ⟨l, Or.inl rfl⟩
    · exact ⟨l, Or.inr rfl⟩

private lemma isTorusWt_mul_pow {n : ℕ} (m : ℕ) {a : Z n} (h : IsTorusWt n a) :
    IsTorusWt n (a * (2 : Z n) ^ m) := by
  obtain ⟨i, rfl | rfl⟩ := h
  · exact ⟨i + m, Or.inl (by rw [pow_add])⟩
  · exact ⟨i + m, Or.inr (by rw [neg_mul, ← pow_add])⟩

private lemma isTorusWt_add_mul_pow {n m b : ℕ} {a : Z n}
    (h : IsTorusWt n (a + (2 : Z n) ^ b)) :
    IsTorusWt n (a * (2 : Z n) ^ m + (2 : Z n) ^ (b + m)) := by
  have := isTorusWt_mul_pow (n := n) m h
  rwa [add_mul, ← pow_add] at this

private lemma one_add_pow_not_isTorusWt {n l : ℕ} (hn : 4 ≤ n) (hl0 : 0 < l)
    (hl : l < n) (h : IsTorusWt n (1 + (2 : Z n) ^ l)) : False := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨m, hm_lt, hm | hm⟩ := (isTorusWt_iff (by omega) _).mp h
  · have hnat : 1 + 2 ^ l = 2 ^ m := by
      apply natCast_inj_of_lt (one_add_pow_lt_N (by omega) hl) (pow_lt_N hn2 hm_lt)
      push_cast; exact hm
    have hm0 : m ≠ 0 := by rintro rfl; have := Nat.two_pow_pos l; omega
    have ho : Odd (1 + 2 ^ l) :=
      (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two (by omega)).one_add
    have he : Even (2 ^ m) := Even.pow_of_ne_zero (a := (2 : ℕ)) even_two hm0
    rw [hnat] at ho
    exact (Nat.not_even_iff_odd.mpr ho) he
  · have hpos : 0 < 1 + 2 ^ l + 2 ^ m := by
      have h1 := Nat.two_pow_pos l; have h2 := Nat.two_pow_pos m; omega
    have hlt : 1 + 2 ^ l + 2 ^ m < 2 * (2 ^ n - 1) := by
      have h1 := pow_lt_N hn2 hl; have h2 := pow_lt_N hn2 hm_lt; omega
    have hzero : ((1 + 2 ^ l + 2 ^ m : ℕ) : Z n) = 0 := by
      push_cast; rw [hm]; ring
    have hnat : 1 + 2 ^ l + 2 ^ m = 2 ^ n - 1 := natCast_sum_eq_zero hpos hlt hzero
    have hnat' : 2 + 2 ^ l + 2 ^ m = 2 ^ n := by
      have h2 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow; omega
    exact two_add_pow_add_pow_ne hn hl hm_lt hnat'

private lemma one_add_pow_isTorusWt {n l : ℕ} (hn : 4 ≤ n) (hl : l < n)
    (h : IsTorusWt n (1 + (2 : Z n) ^ l)) : l = 0 := by
  by_contra hl0
  exact one_add_pow_not_isTorusWt hn (by omega) hl h

private lemma one_add_last_pow_not_isTorusWt {n : ℕ} (hn : 4 ≤ n) :
    ¬ IsTorusWt n (1 + (2 : Z n) ^ (n - 1)) :=
  one_add_pow_not_isTorusWt (l := n - 1) hn (by omega) (by omega)

private lemma neg_one_add_pow_isTorusWt {n l : ℕ} (hn : 4 ≤ n) (hl : l < n)
    (h : IsTorusWt n (-1 + (2 : Z n) ^ l)) : l = 1 ∨ l = n - 1 := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨m, hm_lt, hm | hm⟩ := (isTorusWt_iff (by omega) _).mp h
  · have hm' : (2 : Z n) ^ l = (2 : Z n) ^ m + 1 := by
      calc (2 : Z n) ^ l = -1 + (2 : Z n) ^ l + 1 := by ring
        _ = (2 : Z n) ^ m + 1 := by rw [hm]
    have hlt : 2 ^ m + 1 < 2 ^ n - 1 := by
      have := one_add_pow_lt_N (n := n) (l := m) (by omega) hm_lt; omega
    have hnat : 2 ^ l = 2 ^ m + 1 := by
      apply natCast_inj_of_lt (pow_lt_N hn2 hl) hlt; push_cast; exact hm'
    exact Or.inl (pow_eq_pow_add_one_imp hn hl hm_lt hnat)
  · have hm' : (2 : Z n) ^ l + (2 : Z n) ^ m = 1 := by
      calc (2 : Z n) ^ l + (2 : Z n) ^ m =
          -1 + (2 : Z n) ^ l + 1 + (2 : Z n) ^ m := by ring
        _ = 1 := by rw [hm]; ring
    have hcast : ((2 ^ l + 2 ^ m : ℕ) : Z n) = ((1 : ℕ) : Z n) := by
      push_cast; exact hm'
    have hs2 : 1 < 2 ^ l + 2 ^ m := by
      have h1 := Nat.two_pow_pos l; have h2 := Nat.two_pow_pos m; omega
    have hle : 2 ^ l + 2 ^ m ≤ 2 ^ n := by
      calc 2 ^ l + 2 ^ m ≤ 2 ^ (n - 1) + 2 ^ (n - 1) :=
              add_le_add (Nat.pow_le_pow_right (by norm_num) (by omega))
                (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ = 2 * 2 ^ (n - 1) := (two_mul _).symm
        _ = 2 ^ n := (two_pow_eq_two_mul (by omega)).symm
    have hsum : 2 ^ l + 2 ^ m = 2 ^ n := by
      have hmod : (1 : ℕ) ≡ 2 ^ l + 2 ^ m [MOD 2 ^ n - 1] :=
        ((ZMod.natCast_eq_natCast_iff (2 ^ l + 2 ^ m) 1 (2 ^ n - 1)).mp hcast).symm
      have hdvd : (2 ^ n - 1) ∣ 2 ^ l + 2 ^ m - 1 :=
        (Nat.modEq_iff_dvd' hs2.le).mp hmod
      have hN : 2 ^ n = (2 ^ n - 1) + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
      have hsle : 2 ^ l + 2 ^ m - 1 ≤ 2 ^ n - 1 := Nat.sub_le_sub_right hle 1
      have hlt : 2 ^ l + 2 ^ m - 1 < 2 * (2 ^ n - 1) := by
        have := Nat.one_lt_two_pow (n := n) (by omega)
        omega
      have := Nat.eq_of_dvd_of_lt_two_mul (a := 2 ^ l + 2 ^ m - 1)
        (b := 2 ^ n - 1) (Nat.sub_ne_zero_of_lt hs2) hdvd hlt
      omega
    exact Or.inr (pow_add_pow_eq_two_pow_imp hn hl hm_lt hsum)

private lemma pow_two_zmod_three (i : ℕ) : (2 : ZMod 3) ^ i = 1 ∨ (2 : ZMod 3) ^ i = 2 := by
  have h2 : (2 : ZMod 3) = -1 := by decide
  rw [h2, neg_one_pow_eq_ite]
  by_cases hi : Even i
  · exact Or.inl (by rw [if_pos hi])
  · exact Or.inr (by rw [if_neg hi])

private lemma isTorusWt_two_iff (a : ZMod 3) : IsTorusWt 2 a ↔ a = 1 ∨ a = 2 := by
  constructor
  · rintro ⟨i, rfl | rfl⟩
    · exact pow_two_zmod_three i
    · have h := pow_two_zmod_three i
      rcases h with h | h
      · exact Or.inr (by rw [h]; decide)
      · exact Or.inl (by rw [h]; decide)
  · rintro (rfl | rfl)
    · exact ⟨0, Or.inl (by norm_num)⟩
    · exact ⟨1, Or.inl (by norm_num)⟩

private lemma no_square_zmod_three {a u v : ZMod 3} (hu : u = 1 ∨ u = 2)
    (hv : v = 1 ∨ v = 2) (huv : u ≠ v) (ha : a = 1 ∨ a = 2)
    (h1 : a + u = 1 ∨ a + u = 2) (h2 : a + v = 1 ∨ a + v = 2) : False := by
  revert a u v; decide

private lemma no_square_two {β γ : ℕ} {a : ZMod 3}
    (hβγ : (2 : ZMod 3) ^ β ≠ (2 : ZMod 3) ^ γ)
    (h₀ : IsTorusWt 2 a) (h₁ : IsTorusWt 2 (a + 2 ^ β))
    (h₂ : IsTorusWt 2 (a + 2 ^ γ)) : False := by
  rcases pow_two_zmod_three β with hb | hb <;> rcases pow_two_zmod_three γ with hc | hc
  · exact hβγ (hb.trans hc.symm)
  · have huv : (1 : ZMod 3) ≠ 2 := by have := hβγ; rwa [hb, hc] at this
    exact no_square_zmod_three (Or.inl rfl) (Or.inr rfl) huv ((isTorusWt_two_iff a).mp h₀)
      ((isTorusWt_two_iff (a + 1)).mp (by rwa [hb] at h₁))
      ((isTorusWt_two_iff (a + 2)).mp (by rwa [hc] at h₂))
  · have huv : (2 : ZMod 3) ≠ 1 := by have := hβγ; rwa [hb, hc] at this
    exact no_square_zmod_three (Or.inr rfl) (Or.inl rfl) huv ((isTorusWt_two_iff a).mp h₀)
      ((isTorusWt_two_iff (a + 2)).mp (by rwa [hb] at h₁))
      ((isTorusWt_two_iff (a + 1)).mp (by rwa [hc] at h₂))
  · exact hβγ (hb.trans hc.symm)

private lemma pow_eq_one_of_one_add {n b : ℕ} (hn : 4 ≤ n)
    (h : IsTorusWt n (1 + (2 : Z n) ^ b)) : (2 : Z n) ^ b = 1 := by
  have hbpow : (2 : Z n) ^ b = (2 : Z n) ^ (b % n) := pow_eq_pow_mod_zmod (by omega)
  have hb0 : b % n = 0 := by
    apply one_add_pow_isTorusWt hn (Nat.mod_lt b (by omega))
    rwa [hbpow] at h
  rw [hbpow, hb0, pow_zero]

private lemma pow_eq_two_or_last_of_neg_one_add {n b : ℕ} (hn : 4 ≤ n)
    (h : IsTorusWt n (-1 + (2 : Z n) ^ b)) :
    (2 : Z n) ^ b = 2 ∨ (2 : Z n) ^ b = (2 : Z n) ^ (n - 1) := by
  have hbpow : (2 : Z n) ^ b = (2 : Z n) ^ (b % n) := pow_eq_pow_mod_zmod (by omega)
  have hbw : IsTorusWt n (-1 + (2 : Z n) ^ (b % n)) := by rwa [hbpow] at h
  rcases neg_one_add_pow_isTorusWt hn (Nat.mod_lt b (by omega)) hbw with hb | hb
  · exact Or.inl (by rw [hbpow, hb]; norm_num)
  · exact Or.inr (by rw [hbpow, hb])

private lemma no_square_one {n : ℕ} (hn : 4 ≤ n) {b c : ℕ}
    (hbc : (2 : Z n) ^ b ≠ (2 : Z n) ^ c)
    (h₁ : IsTorusWt n (1 + (2 : Z n) ^ b))
    (h₂ : IsTorusWt n (1 + (2 : Z n) ^ c)) : False :=
  hbc ((pow_eq_one_of_one_add hn h₁).trans (pow_eq_one_of_one_add hn h₂).symm)

private lemma no_square_neg_one {n : ℕ} (hn : 4 ≤ n) {b c : ℕ}
    (hbc : (2 : Z n) ^ b ≠ (2 : Z n) ^ c)
    (h₁ : IsTorusWt n (-1 + (2 : Z n) ^ b))
    (h₂ : IsTorusWt n (-1 + (2 : Z n) ^ c))
    (h₃ : IsTorusWt n (-1 + (2 : Z n) ^ b + (2 : Z n) ^ c)) : False := by
  have hb := pow_eq_two_or_last_of_neg_one_add hn h₁
  have hc := pow_eq_two_or_last_of_neg_one_add hn h₂
  have hsum : (2 : Z n) ^ b + (2 : Z n) ^ c = 2 + (2 : Z n) ^ (n - 1) := by
    rcases hb with hb | hb <;> rcases hc with hc | hc
    · exact absurd (hb.trans hc.symm) hbc
    · calc (2 : Z n) ^ b + (2 : Z n) ^ c = 2 + (2 : Z n) ^ c := by
            conv_lhs => arg 1; rw [hb]
        _ = 2 + (2 : Z n) ^ (n - 1) := by conv_lhs => arg 2; rw [hc]
    · calc (2 : Z n) ^ b + (2 : Z n) ^ c = (2 : Z n) ^ (n - 1) + (2 : Z n) ^ c := by
            conv_lhs => arg 1; rw [hb]
        _ = (2 : Z n) ^ (n - 1) + 2 := by conv_lhs => arg 2; rw [hc]
        _ = 2 + (2 : Z n) ^ (n - 1) := by ring
    · exact absurd (hb.trans hc.symm) hbc
  have h₃' : IsTorusWt n (1 + (2 : Z n) ^ (n - 1)) := by
    have h : -1 + (2 : Z n) ^ b + (2 : Z n) ^ c = 1 + (2 : Z n) ^ (n - 1) := by
      calc -1 + (2 : Z n) ^ b + (2 : Z n) ^ c =
          -1 + ((2 : Z n) ^ b + (2 : Z n) ^ c) := by ring
        _ = -1 + (2 + (2 : Z n) ^ (n - 1)) := by rw [hsum]
        _ = 1 + (2 : Z n) ^ (n - 1) := by ring
    rwa [h] at h₃
  exact one_add_last_pow_not_isTorusWt hn h₃'

private lemma normalized_square {n : ℕ} (hn : 4 ≤ n) {β γ : ℕ} {a : Z n}
    (hβγ : (2 : Z n) ^ β ≠ 2 ^ γ) (h₀ : IsTorusWt n a)
    (h₁ : IsTorusWt n (a + 2 ^ β)) (h₂ : IsTorusWt n (a + 2 ^ γ))
    (h₃ : IsTorusWt n (a + 2 ^ β + 2 ^ γ)) :
    ∃ (ε : Z n) (m : ℕ), (ε = 1 ∨ ε = -1) ∧ (2 : Z n) ^ (β + m) ≠ 2 ^ (γ + m) ∧
      IsTorusWt n (ε + 2 ^ (β + m)) ∧ IsTorusWt n (ε + 2 ^ (γ + m)) ∧
      IsTorusWt n (ε + 2 ^ (β + m) + 2 ^ (γ + m)) := by
  obtain ⟨i, hi⟩ := h₀
  set m : ℕ := (n - 1) * i with hm_def
  have hm_pow : (2 : Z n) ^ (i + m) = 1 := by
    have hexp : i + m = n * i := by
      rw [hm_def]; conv_rhs => rw [show n = n - 1 + 1 by omega]
      rw [Nat.add_mul, one_mul]; omega
    rw [hexp, pow_mul, pow_eq_one_zmod (by omega), one_pow]
  have hε : a * (2 : Z n) ^ m = 1 ∨ a * (2 : Z n) ^ m = -1 := by
    rcases hi with hi | hi
    · exact Or.inl (by rw [hi, ← pow_add, hm_pow])
    · exact Or.inr (by rw [hi, neg_mul, ← pow_add, hm_pow])
  have hβγ' : (2 : Z n) ^ (β + m) ≠ 2 ^ (γ + m) := by
    intro heq
    have hu : IsUnit ((2 : Z n) ^ m) := IsUnit.pow m (isUnit_two_zmod (by omega))
    apply hβγ
    rw [pow_add, pow_add] at heq
    exact hu.mul_right_cancel heq
  exact ⟨a * (2 : Z n) ^ m, m, hε, hβγ',
    isTorusWt_add_mul_pow (n := n) (m := m) (b := β) (a := a) h₁,
    isTorusWt_add_mul_pow (n := n) (m := m) (b := γ) (a := a) h₂,
    (by
      have := isTorusWt_mul_pow (n := n) m h₃
      rwa [add_mul, add_mul, ← pow_add, ← pow_add] at this)⟩

theorem not_isTorusWt_square {n : ℕ} (hn : n = 2 ∨ 4 ≤ n) {β γ : ℕ}
    (hβγ : (2 : ZMod (2 ^ n - 1)) ^ β ≠ 2 ^ γ) {a : ZMod (2 ^ n - 1)}
    (h₀ : IsTorusWt n a) (h₁ : IsTorusWt n (a + 2 ^ β))
    (h₂ : IsTorusWt n (a + 2 ^ γ))
    (h₃ : IsTorusWt n (a + 2 ^ β + 2 ^ γ)) : False := by
  rcases hn with rfl | hn4
  · exact no_square_two hβγ h₀ h₁ h₂
  · obtain ⟨ε, m, hε, hβγ', h₁', h₂', h₃'⟩ := normalized_square hn4 hβγ h₀ h₁ h₂ h₃
    rcases hε with rfl | rfl
    · exact no_square_one hn4 hβγ' h₁' h₂'
    · exact no_square_neg_one hn4 hβγ' h₁' h₂' h₃'

theorem two_pow_succ_ne {n b c : ℕ} (hn : 2 ≤ n) (hb : b < n) (hc : c < n)
    (hbc : b ≠ c) : (2 : ZMod (2 ^ n - 1)) ^ (b + 1) ≠ 2 ^ (c + 1) := by
  intro h
  have hu : IsUnit (2 : ZMod (2 ^ n - 1)) := isUnit_two_zmod (by omega)
  have hbc' : (2 : ZMod (2 ^ n - 1)) ^ b = (2 : ZMod (2 ^ n - 1)) ^ c := by
    rw [pow_succ, pow_succ] at h
    exact hu.mul_right_cancel h
  apply hbc
  apply Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))
  exact natCast_inj_of_lt (pow_lt_N hn hb) (pow_lt_N hn hc) (by push_cast; exact hbc')

end CFSG.RepresentationTheory.SL2NatSum
