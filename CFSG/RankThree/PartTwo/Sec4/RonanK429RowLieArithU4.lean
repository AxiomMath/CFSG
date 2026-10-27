module

public import CFSG.RankThree.PartTwo.Sec19.Step1917StepsOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

private theorem u4Arith_two_pow_eq {a b X Y : ℕ} (hX : Odd X) (hY : Odd Y)
    (h : 2 ^ a * X = 2 ^ b * Y) : a = b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX0 : X ≠ 0 := by obtain ⟨k, hk⟩ := hX; omega
  have hY0 : Y ≠ 0 := by obtain ⟨k, hk⟩ := hY; omega
  have hX2 : ¬ 2 ∣ X := by obtain ⟨k, hk⟩ := hX; omega
  have hY2 : ¬ 2 ∣ Y := by obtain ⟨k, hk⟩ := hY; omega
  have h1 := congrArg (padicValNat 2) h
  rw [padicValNat.mul (pow_ne_zero a (by norm_num : (2 : ℕ) ≠ 0)) hX0,
    padicValNat.mul (pow_ne_zero b (by norm_num : (2 : ℕ) ≠ 0)) hY0,
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hX2,
    padicValNat.eq_zero_of_not_dvd hY2] at h1
  omega

private theorem u4Arith_U_odd {k : ℕ} (hk : 1 ≤ k) :
    Odd (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1) * 3) := by
  have hE : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hE2 : 2 ∣ (2 ^ k) ^ 2 := dvd_pow hE (by norm_num)
  have hE3 : 2 ∣ (2 ^ k) ^ 3 := dvd_pow hE (by norm_num)
  have hE4 : 2 ∣ (2 ^ k) ^ 4 := dvd_pow hE (by norm_num)
  have hpos2 : 0 < (2 ^ k) ^ 2 := by positivity
  have hpos3 : 0 < (2 ^ k) ^ 3 := by positivity
  have hpos4 : 0 < (2 ^ k) ^ 4 := by positivity
  have o2 : Odd ((2 ^ k) ^ 2 - 1) := Nat.odd_iff.mpr (by omega)
  have o3 : Odd ((2 ^ k) ^ 3 + 1) := Nat.odd_iff.mpr (by omega)
  have o4 : Odd ((2 ^ k) ^ 4 - 1) := Nat.odd_iff.mpr (by omega)
  exact Nat.odd_mul.mpr ⟨Nat.odd_mul.mpr ⟨Nat.odd_mul.mpr ⟨o2, o3⟩, o4⟩,
    Nat.odd_iff.mpr (by norm_num)⟩

private theorem u4Arith_V_odd {e : ℕ} (he : 1 ≤ e) :
    Odd (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1)) ∧
      Odd (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1)) := by
  have hE : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
  have hE2 : 2 ∣ (2 ^ e) ^ 2 := dvd_pow hE (by norm_num)
  have hE3 : 2 ∣ (2 ^ e) ^ 3 := dvd_pow hE (by norm_num)
  have hpos2 : 0 < (2 ^ e) ^ 2 := by positivity
  have hpos3 : 0 < (2 ^ e) ^ 3 := by positivity
  have o2 : Odd ((2 ^ e) ^ 2 - 1) := Nat.odd_iff.mpr (by omega)
  have o3 : Odd ((2 ^ e) ^ 3 - 1) := Nat.odd_iff.mpr (by omega)
  have o3' : Odd ((2 ^ e) ^ 3 + 1) := Nat.odd_iff.mpr (by omega)
  exact ⟨Nat.odd_mul.mpr ⟨o2, o3⟩, Nat.odd_mul.mpr ⟨o2, o3'⟩⟩

private theorem u4Arith_two_exp {k e V : ℕ} (hk : 1 ≤ k) (hV : Odd V)
    (h : (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) * 3 =
      (2 ^ e) ^ 3 * V) : e = 2 * k := by
  have key : 2 ^ (6 * k) * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1) * 3) =
      2 ^ (3 * e) * V := by
    rw [show (2 : ℕ) ^ (6 * k) = (2 ^ k) ^ 6 by ring,
      show (2 : ℕ) ^ (3 * e) = (2 ^ e) ^ 3 by ring]
    calc (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1) * 3)
        = (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) * 3 := by
          ring
      _ = (2 ^ e) ^ 3 * V := h
  have h6 : 6 * k = 3 * e := u4Arith_two_pow_eq (u4Arith_U_odd hk) hV key
  omega

private theorem u4Arith_S_lt {x : ℕ} (hx : 4 ≤ x) :
    (x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) < (x ^ 3 - 1) ^ 3 := by
  have h2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ x ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h3, h4]
  have ht : (4 : ℤ) ≤ (x : ℤ) := by exact_mod_cast hx
  have ht0 : (0 : ℤ) ≤ (x : ℤ) := by positivity
  have ht2 : (16 : ℤ) ≤ (x : ℤ) ^ 2 := by nlinarith
  nlinarith [mul_nonneg (pow_nonneg ht0 6) (sub_nonneg.mpr ht), pow_nonneg ht0 5,
    pow_nonneg ht0 4, pow_nonneg ht0 3]

private theorem u4Arith_pure_L3 {x : ℕ} (hx : 2 ≤ x)
    (h : x ^ 6 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1)) * 3 =
      (x ^ 2) ^ 3 * (((x ^ 2) ^ 2 - 1) * ((x ^ 2) ^ 3 - 1))) : False := by
  have hx0 : 0 < x ^ 6 := pow_pos (by omega) 6
  have hx4 : 16 ≤ x ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ x ^ 4 := Nat.pow_le_pow_left hx 4
  have e1 : (x ^ 2) ^ 3 = x ^ 6 := by ring
  have e2 : (x ^ 2) ^ 2 = x ^ 4 := by ring
  rw [e1, e2] at h
  have hA : x ^ 6 * ((x ^ 4 - 1) * (3 * (x ^ 2 - 1) * (x ^ 3 + 1))) =
      x ^ 6 * ((x ^ 4 - 1) * (x ^ 6 - 1)) := by
    calc x ^ 6 * ((x ^ 4 - 1) * (3 * (x ^ 2 - 1) * (x ^ 3 + 1)))
        = x ^ 6 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1)) * 3 := by ring
      _ = x ^ 6 * ((x ^ 4 - 1) * (x ^ 6 - 1)) := h
  have hC := Nat.eq_of_mul_eq_mul_left (by omega : 0 < x ^ 4 - 1)
    (Nat.eq_of_mul_eq_mul_left hx0 hA)
  obtain ⟨u, hu⟩ : ∃ u, x ^ 3 = u + 1 :=
    ⟨x ^ 3 - 1, by have := Nat.one_le_pow 3 x (by omega); omega⟩
  have hx6 : x ^ 6 - 1 = u * (x ^ 3 + 1) := by
    have h6 : x ^ 6 = (x ^ 3) ^ 2 := by ring
    have hsq : (u + 1) ^ 2 = u * (u + 1 + 1) + 1 := by ring
    rw [h6, hu, hsq]
    omega
  rw [hx6] at hC
  have hD : 3 * (x ^ 2 - 1) = u := Nat.eq_of_mul_eq_mul_right (by omega) hC
  have hx2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  rcases Nat.lt_or_ge x 3 with h3 | h3
  · obtain rfl : x = 2 := by omega
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
    rw [h4] at hD
    rw [h8] at hu
    omega
  · have h3x : 3 * x ^ 2 ≤ x ^ 3 := by
      calc 3 * x ^ 2 ≤ x * x ^ 2 := Nat.mul_le_mul_right _ h3
        _ = x ^ 3 := by ring
    omega

private theorem u4Arith_pure_U3 {x : ℕ} (hx : 2 ≤ x)
    (h : x ^ 6 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1)) * 3 =
      (x ^ 2) ^ 3 * (((x ^ 2) ^ 2 - 1) * ((x ^ 2) ^ 3 + 1))) : False := by
  have hx0 : 0 < x ^ 6 := pow_pos (by omega) 6
  have hx4 : 16 ≤ x ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ x ^ 4 := Nat.pow_le_pow_left hx 4
  have e1 : (x ^ 2) ^ 3 = x ^ 6 := by ring
  have e2 : (x ^ 2) ^ 2 = x ^ 4 := by ring
  rw [e1, e2] at h
  have hA : x ^ 6 * ((x ^ 4 - 1) * (3 * (x ^ 2 - 1) * (x ^ 3 + 1))) =
      x ^ 6 * ((x ^ 4 - 1) * (x ^ 6 + 1)) := by
    calc x ^ 6 * ((x ^ 4 - 1) * (3 * (x ^ 2 - 1) * (x ^ 3 + 1)))
        = x ^ 6 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1)) * 3 := by ring
      _ = x ^ 6 * ((x ^ 4 - 1) * (x ^ 6 + 1)) := h
  have hC := Nat.eq_of_mul_eq_mul_left (by omega : 0 < x ^ 4 - 1)
    (Nat.eq_of_mul_eq_mul_left hx0 hA)
  have hdvd : x ^ 3 + 1 ∣ x ^ 6 + 1 := ⟨3 * (x ^ 2 - 1), by rw [← hC]; ring⟩
  have hsum : x ^ 3 + 1 ∣ (x ^ 6 + 1) + 2 * x ^ 3 := ⟨x ^ 3 + 1, by ring⟩
  have h2x : x ^ 3 + 1 ∣ 2 * x ^ 3 := (Nat.dvd_add_right hdvd).mp hsum
  have h2 : x ^ 3 + 1 ∣ 2 * x ^ 3 + 2 := ⟨2, by ring⟩
  have h2' : x ^ 3 + 1 ∣ 2 := (Nat.dvd_add_right h2x).mp h2
  have hle : x ^ 3 + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) h2'
  have h8 : 8 ≤ x ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
  omega

private theorem u4Arith_odd {x k r T : ℕ} (hxk : x = 2 ^ k) (hk : 1 ≤ k) (hr : Odd r)
    (hr3 : ¬ 3 ∣ r) (hr5 : 5 ≤ r) (hT : T = r ^ 3 - 1 ∨ T = r ^ 3 + 1)
    (h : x ^ 6 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1)) * 3 = r ^ 3 * ((r ^ 2 - 1) * T)) :
    False := by
  have hx2 : 2 ≤ x := by
    subst hxk
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
  have hpow : (2 : ℕ) ^ (6 * k) = x ^ 6 := by
    subst hxk
    ring
  have hx2' : 4 ≤ x ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ x ^ 2 := Nat.pow_le_pow_left hx2 2
  have hx4' : 16 ≤ x ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ x ^ 4 := Nat.pow_le_pow_left hx2 4
  have hSpos : 0 < (x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hdvd6 : r ^ 3 ∣ 3 * (2 ^ (6 * k) * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1))) :=
    ⟨(r ^ 2 - 1) * T, by rw [hpow, ← h]; ring⟩
  have hcube : r ^ 3 ∣ (x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) :=
    CFSG.RankThree.PartTwo.Sec19.Step1917Steps.pow_three_dvd_of_coprime hr hr3 hdvd6
  have hrS : r ^ 3 ≤ (x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) := Nat.le_of_dvd hSpos hcube
  have hE : r ^ 3 * (r ^ 2 - 1) * T =
      2 ^ (6 * k) * (3 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1))) := by
    rw [hpow]
    calc r ^ 3 * (r ^ 2 - 1) * T = r ^ 3 * ((r ^ 2 - 1) * T) := by ring
      _ = x ^ 6 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1)) * 3 := h.symm
      _ = x ^ 6 * (3 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1))) := by ring
  have hdvd2 : 2 ^ (6 * k) ∣ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 - 1) ∨
      2 ^ (6 * k) ∣ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 + 1) := by
    rcases hT with rfl | rfl
    · exact Or.inl ⟨_, hE⟩
    · exact Or.inr ⟨_, hE⟩
  have hle := CFSG.RankThree.PartTwo.Sec19.Step1917Steps.two_pow_le_of_dvd_sl3Order hr
    (by omega) (by omega) hdvd2
  have hx3 : (2 : ℕ) ^ (6 * k / 2) = x ^ 3 := by
    rw [show 6 * k / 2 = 3 * k by omega]
    subst hxk
    ring
  rw [hx3] at hle
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  ·
    obtain rfl : k = 1 := by omega
    have hx' : x = 2 := by
      subst hxk
      norm_num
    subst hx'
    have hr7 : 7 ≤ r := by
      norm_num at hle
      omega
    have h405 : r ^ 3 ≤ 405 := by
      norm_num at hrS
      omega
    have hr7' : r ≤ 7 := by
      by_contra hc
      have hr8 : 512 ≤ r ^ 3 := by
        calc (512 : ℕ) = 8 ^ 3 := by norm_num
          _ ≤ r ^ 3 := Nat.pow_le_pow_left (by omega) 3
      omega
    have hr7e : r = 7 := by omega
    subst hr7e
    norm_num at hcube
  · have hx4 : 4 ≤ x := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
        _ = x := hxk.symm
    have hsub : x ^ 3 - 1 ≤ r := by omega
    have hpow3 : (x ^ 3 - 1) ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left hsub 3
    have hlt : (x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) < r ^ 3 :=
      lt_of_lt_of_le (u4Arith_S_lt hx4) hpow3
    exact absurd (hlt.trans_le hrS) (lt_irrefl _)

theorem u4_mul_three_ne_L3 {k p e : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hp3 : p ≠ 3) (he : 1 ≤ e) :
    (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) * 3 ≠
      (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) := by
  intro h
  have hx2 : 2 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
  by_cases hp2 : p = 2
  · subst hp2
    have he2 : e = 2 * k := u4Arith_two_exp hk (u4Arith_V_odd he).1 h
    subst he2
    rw [show (2 : ℕ) ^ (2 * k) = (2 ^ k) ^ 2 by ring] at h
    exact u4Arith_pure_L3 hx2 h
  · have hodd_p : Odd p := hp.odd_of_ne_two hp2
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h2' := Nat.odd_iff.mp hodd_p
      omega
    have hr5 : 5 ≤ p ^ e := le_trans hp5 (Nat.le_self_pow (by omega) p)
    have hr3 : ¬ 3 ∣ p ^ e := fun h3 =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)).symm
    exact u4Arith_odd (x := 2 ^ k) (k := k) (r := p ^ e) (T := (p ^ e) ^ 3 - 1) rfl hk
      (hodd_p.pow : Odd (p ^ e)) hr3 hr5 (Or.inl rfl) h

theorem u4_mul_three_ne_U3 {k p e : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hp3 : p ≠ 3) (he : 1 ≤ e) :
    (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) * 3 ≠
      (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) := by
  intro h
  have hx2 : 2 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
  by_cases hp2 : p = 2
  · subst hp2
    have he2 : e = 2 * k := u4Arith_two_exp hk (u4Arith_V_odd he).2 h
    subst he2
    rw [show (2 : ℕ) ^ (2 * k) = (2 ^ k) ^ 2 by ring] at h
    exact u4Arith_pure_U3 hx2 h
  · have hodd_p : Odd p := hp.odd_of_ne_two hp2
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h2' := Nat.odd_iff.mp hodd_p
      omega
    have hr5 : 5 ≤ p ^ e := le_trans hp5 (Nat.le_self_pow (by omega) p)
    have hr3 : ¬ 3 ∣ p ^ e := fun h3 =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)).symm
    exact u4Arith_odd (x := 2 ^ k) (k := k) (r := p ^ e) (T := (p ^ e) ^ 3 + 1) rfl hk
      (hodd_p.pow : Odd (p ^ e)) hr3 hr5 (Or.inr rfl) h

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
