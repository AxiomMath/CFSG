module

public import CFSG.Quasithin.Background.GoldschmidtB69DeepFam

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders

namespace B69

theorem cubic_no_6048 (Q g X c : ℕ) (hg : 0 < g) (hg2 : g ≤ 2) (hc : Odd c)
    (h : X * g + Q = Q ^ 3) (hX : X * c = 6048) : False := by
  have hX0 : 0 < X := by
    rcases Nat.eq_zero_or_pos X with rfl | h0
    · omega
    · exact h0
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with rfl | h0
    · omega
    · exact h0
  have hXle : X ≤ 6048 := by nlinarith
  have hQ : Q ≤ 23 := by
    by_contra hlt
    push Not at hlt
    have h1 : X * g ≤ 12096 := by nlinarith
    have h3 : 576 * Q ≤ Q ^ 3 := by
      calc 576 * Q = 24 ^ 2 * Q := by norm_num
        _ ≤ Q ^ 2 * Q := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hlt 2)
        _ = Q ^ 3 := by ring
    omega
  have hXd : X = (Q ^ 3 - Q) / g := Nat.eq_div_of_mul_eq_left hg.ne' (by omega)
  subst hXd
  obtain ⟨c', rfl⟩ := hc
  interval_cases Q <;> interval_cases g <;> norm_num at hX <;> omega

theorem big_three_6048 {q g X : ℕ} (hq : 4 ≤ q) (hg : g ≤ 3)
    (h : X * g = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∨
      X * g = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) :
    6048 < X := by
  have h1 : 4 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 4 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
  have h3 : 4 ^ 3 - 1 ≤ q ^ 3 - 1 := Nat.sub_le_sub_right h1 1
  have h3' : 4 ^ 3 - 1 ≤ q ^ 3 + 1 := by omega
  have h4 : 4 ^ 3 * ((4 ^ 2 - 1) * (4 ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3')
  have h5 : 4 ^ 3 * ((4 ^ 2 - 1) * (4 ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  by_contra hX
  push Not at hX
  have h6 : X * g ≤ 6048 * 3 := Nat.mul_le_mul hX hg
  rcases h with h | h <;> norm_num at h4 h5 h6 <;> omega

theorem big_four_6048 {q X : ℕ} (hq : 4 ≤ q) (h : X = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) :
    6048 < X := by
  have h1 : 4 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have h2 : 4 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
  have h3 : 4 ^ 4 - 1 ≤ q ^ 4 - 1 := Nat.sub_le_sub_right h1 1
  have h4 : 4 ^ 4 * ((4 ^ 2 - 1) * (4 ^ 4 - 1)) ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  rw [h]
  norm_num at h4
  omega

namespace E22FamC

theorem not_card_6048 {F : Type} [Group F] (hF : E22FamC F)
    {c : ℕ} (hc : Odd c)
    (h : Nat.card F * c = 6048) : False := by
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by intro h0; rw [h0] at h; omega)
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with rfl | h0
    · omega
    · exact h0
  have hle : Nat.card F ≤ 6048 := by nlinarith
  obtain ⟨c', rfl⟩ := hc
  rcases hF with ⟨p, e, hp⟩ | ⟨m, hm⟩ | ⟨m, hm⟩ | ⟨m, hm1, hm⟩ | ⟨m, hm1, hm⟩ | ⟨p, hp2, hp4, hp⟩ |
    ⟨p, hp2, hp4, hp⟩
  · have h1 := card_psl_two_mul hp
    have hg1 : 0 < Nat.gcd 2 (p ^ e - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hg2 : Nat.gcd 2 (p ^ e - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    exact cubic_no_6048 (p ^ e) _ _ (2 * c' + 1) hg1 hg2 ⟨c', rfl⟩ h1 h
  · obtain ⟨-, a, ha, F', _, _, hfa, hF', ⟨e⟩⟩ := hm
    have hF'' : Nat.card F' = 2 ^ (2 * a + 1) := by rw [hF', hfa]
    have hc : Nat.card F = CFSG.Open.ordSuzuki (2 ^ m) := by
      rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hF'', hfa, CFSG.Open.ordSuzuki]
      exact Nat.mul_right_comm _ _ _
    have hq8 : 8 ≤ 2 ^ m := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [CFSG.Open.ordSuzuki] at hc
    have h1 : 8 ^ 2 * (8 ^ 2 + 1) * (8 - 1) ≤ (2 ^ m) ^ 2 * ((2 ^ m) ^ 2 + 1) * (2 ^ m - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hq8 2)
        (by have := Nat.pow_le_pow_left hq8 2; omega)) (Nat.sub_le_sub_right hq8 1)
    rw [← hc] at h1
    norm_num at h1
    omega
  · have hn2 : 2 ≤ m := by
      obtain ⟨-, hf, -, h32⟩ := hm.1
      by_contra hlt
      have : m = 1 := by omega
      subst this
      exact h32 (by norm_num)
    have h1 := card_psu_three_mul hm
    have hg : Nat.gcd 3 (2 ^ m + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have hq : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hn2
    have := big_three_6048 hq hg (Or.inl h1)
    omega
  · have h1 := card_psl_three_mul hm
    have hg : Nat.gcd 3 (2 ^ m - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl : m = 1 := by omega
      have hg1 : Nat.gcd 3 (2 ^ 1 - 1) = 1 := by norm_num
      rw [hg1] at h1
      norm_num at h1
      rw [h1] at h
      omega
    · have hq : 4 ≤ 2 ^ m := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      have := big_three_6048 hq hg (Or.inr h1)
      omega
  · unfold E2.IsSp4Prime at hm
    split_ifs at hm with h1
    · obtain ⟨e⟩ := hm
      have hc : Nat.card F = 360 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      rw [hc] at h
      omega
    · have hc := card_psp_four hm
      have hq : 4 ≤ 2 ^ m := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := big_four_6048 hq hc
      omega
  · have hpp : p.Prime := hp.1.1
    have h1 := card_psu_three_mul hp
    rw [pow_one] at h1
    have hg : Nat.gcd 3 (p + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have hq : 4 ≤ p := by have := hpp.two_le; omega
    have := big_three_6048 hq hg (Or.inl h1)
    omega
  · have hpp : p.Prime := hp.1.1
    have h1 := card_psl_three_mul hp
    rw [pow_one] at h1
    have hg : Nat.gcd 3 (p - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    rcases Nat.lt_or_ge p 4 with hp3 | hp3
    · have hp3' : p = 3 := by have := hpp.two_le; omega
      subst hp3'
      have hg1 : Nat.gcd 3 (3 - 1) = 1 := by norm_num
      rw [hg1] at h1
      norm_num at h1
      rw [h1] at h
      omega
    · have := big_three_6048 hp3 hg (Or.inr h1)
      omega

end E22FamC

end B69

end CFSG.Quasithin
