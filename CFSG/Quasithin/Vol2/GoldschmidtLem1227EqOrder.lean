module

public import CFSG.Quasithin.Background.B69Num

public section

namespace CFSG.Quasithin.H13

open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Quasithin.B69

namespace Lem1227Eq

@[expose] def SmallOrder (N : ℕ) : Prop := N = 168 ∨ N = 360 ∨ N = 2520 ∨ N = 6048

theorem SmallOrder.le {N : ℕ} (h : SmallOrder N) : N ≤ 6048 := by
  rcases h with rfl | rfl | rfl | rfl <;> norm_num

theorem psl_two_small {X : Type} [Group X] {p e : ℕ} (h : IsPSL 2 p e X)
    (hN : SmallOrder (Nat.card X)) : p ^ e = 7 ∨ p ^ e = 9 := by
  have h1 := B69.card_psl_two_mul h
  have hNle := hN.le
  generalize p ^ e = q at h1 ⊢
  generalize Nat.card X = N at h1 hN hNle
  have hg : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
  have hq : q ≤ 23 := by
    by_contra hq
    push Not at hq
    have h2 : N * Nat.gcd 2 (q - 1) ≤ 6048 * 2 := Nat.mul_le_mul hNle hg
    have h3 : 576 * q ≤ q ^ 3 := by nlinarith [Nat.mul_le_mul hq hq]
    omega
  interval_cases q <;> rcases hN with rfl | rfl | rfl | rfl <;>
    first | (left; rfl) | (right; rfl) | (exfalso; norm_num at h1)

theorem sz_small {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (h : IsSz n X) (hN : SmallOrder (Nat.card X)) : False := by
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := h
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have hc : Nat.card X = CFSG.Open.ordSuzuki (2 ^ n) := by
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hF', hfa, CFSG.Open.ordSuzuki]
    exact Nat.mul_right_comm _ _ _
  have hq : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hNle := hN.le
  rw [hc, CFSG.Open.ordSuzuki] at hNle
  generalize 2 ^ n = q at hq hNle
  have h1 : 8 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h2 : 8 ^ 2 + 1 ≤ q ^ 2 + 1 := by omega
  have h3 : 8 - 1 ≤ q - 1 := by omega
  have h4 := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  norm_num at h4
  omega

theorem psu_three_two_small {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n) (h : IsPSU 3 2 n X)
    (hN : SmallOrder (Nat.card X)) : False := by
  have h1 := B69.card_psu_three_mul h
  have hNle := hN.le
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  generalize 2 ^ n = q at h1 hq
  generalize Nat.card X = N at h1 hNle
  have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have h2 : N * Nat.gcd 3 (q + 1) ≤ 6048 * 3 := Nat.mul_le_mul hNle hg
  have h3 : 4 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h4 : 4 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
  have h5 : 4 ^ 3 + 1 ≤ q ^ 3 + 1 := by omega
  have h6 := Nat.mul_le_mul h3 (Nat.mul_le_mul h4 h5)
  norm_num at h6
  omega

theorem psl_three_two_small {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n) (h : IsPSL 3 2 n X)
    (hN : SmallOrder (Nat.card X)) : n = 1 ∧ Nat.card X = 168 := by
  have h1 := B69.card_psl_three_mul h
  have hNle := hN.le
  by_cases hn1 : n = 1
  · subst hn1
    refine ⟨rfl, ?_⟩
    norm_num at h1
    rcases hN with h | h | h | h <;> rw [h] at h1 <;> omega
  · exfalso
    have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize 2 ^ n = q at h1 hq
    generalize Nat.card X = N at h1 hNle
    have hg : Nat.gcd 3 (q - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have h2 : N * Nat.gcd 3 (q - 1) ≤ 6048 * 3 := Nat.mul_le_mul hNle hg
    have h3 : 4 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    have h4 : 4 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h5 : 4 ^ 3 - 1 ≤ q ^ 3 - 1 := Nat.sub_le_sub_right h3 1
    have h6 := Nat.mul_le_mul h3 (Nat.mul_le_mul h4 h5)
    norm_num at h6
    omega

theorem sp4Prime_small {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n) (h : E2.IsSp4Prime n X)
    (hN : SmallOrder (Nat.card X)) : n = 1 ∧ IsAlt 6 X ∧ Nat.card X = 360 := by
  have hNle := hN.le
  unfold E2.IsSp4Prime at h
  split_ifs at h with h1
  · obtain ⟨e⟩ := h
    refine ⟨h1, ⟨e⟩, ?_⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  · exfalso
    have hc := B69.card_psp_four h
    have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize 2 ^ n = q at hc hq
    generalize Nat.card X = N at hc hNle
    have h3 : 4 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    have h4 : 4 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h5 : 4 ^ 4 - 1 ≤ q ^ 4 - 1 := Nat.sub_le_sub_right h3 1
    have h6 := Nat.mul_le_mul h3 (Nat.mul_le_mul h4 h5)
    norm_num at h6
    omega

theorem psl_three_odd_small {X : Type} [Group X] {p : ℕ} (hp2 : p ≠ 2) (h : IsPSL 3 p 1 X)
    (hN : SmallOrder (Nat.card X)) : False := by
  have hpp : p.Prime := h.1.1
  have h1 := B69.card_psl_three_mul h
  have hNle := hN.le
  rw [pow_one] at h1
  have hp3 : 3 ≤ p := by
    have := hpp.two_le
    omega
  generalize Nat.card X = N at h1 hN hNle
  have hg : Nat.gcd 3 (p - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have h2 : N * Nat.gcd 3 (p - 1) ≤ 6048 * 3 := Nat.mul_le_mul hNle hg
  by_cases hp5 : 5 ≤ p
  · have h3 : 5 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp5 3
    have h4 : 5 ^ 2 - 1 ≤ p ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hp5 2) 1
    have h5 : 5 ^ 3 - 1 ≤ p ^ 3 - 1 := Nat.sub_le_sub_right h3 1
    have h6 := Nat.mul_le_mul h3 (Nat.mul_le_mul h4 h5)
    norm_num at h6
    omega
  · have : p = 3 ∨ p = 4 := by omega
    rcases this with rfl | rfl
    · norm_num at h1
      rcases hN with rfl | rfl | rfl | rfl <;> omega
    · exact absurd hpp (by norm_num)

theorem psu_three_odd_small {X : Type} [Group X] {p : ℕ} (hp2 : p ≠ 2) (h : IsPSU 3 p 1 X)
    (hN : SmallOrder (Nat.card X)) : p = 3 := by
  have hpp : p.Prime := h.1.1
  have h1 := B69.card_psu_three_mul h
  have hNle := hN.le
  rw [pow_one] at h1
  have hp3 : 3 ≤ p := by
    have := hpp.two_le
    omega
  generalize Nat.card X = N at h1 hN hNle
  have hg : Nat.gcd 3 (p + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have h2 : N * Nat.gcd 3 (p + 1) ≤ 6048 * 3 := Nat.mul_le_mul hNle hg
  by_cases hp5 : 5 ≤ p
  · exfalso
    have h3 : 5 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp5 3
    have h4 : 5 ^ 2 - 1 ≤ p ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hp5 2) 1
    have h5 : 5 ^ 3 + 1 ≤ p ^ 3 + 1 := by omega
    have h6 := Nat.mul_le_mul h3 (Nat.mul_le_mul h4 h5)
    norm_num at h6
    omega
  · have : p = 3 ∨ p = 4 := by omega
    rcases this with h | rfl
    · exact h
    · exact absurd hpp (by norm_num)

@[expose] def E22TwoAlt (X : Type) [Group X] (D A O : Prop) : Prop :=
  (∃ n : ℕ, E2.IsBenderOf n X) ∨
  (∃ n : ℕ, 1 ≤ n ∧ (IsPSL 3 2 n X ∨ E2.IsSp4Prime n X) ∧ D) ∨
  (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) ∧
    IsPSL 2 p e X ∧ A) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ((p % 4 = 1 ∧ IsPSU 3 p 1 X) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 X ∧ O)))

theorem two_pow_ne {n : ℕ} (hn : 1 ≤ n) : 2 ^ n ≠ 7 ∧ 2 ^ n ≠ 9 := by
  have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  omega

theorem prime_pow_ne_nine {p e : ℕ} (hp : p.Prime) (hp3 : 3 < p) (he : e = 1 ∨ e = 2) :
    p ^ e ≠ 9 := by
  intro h
  rcases he with rfl | rfl
  · rw [pow_one] at h
    exact absurd (h ▸ hp) (by norm_num)
  · have : p ≤ 3 := by nlinarith
    omega

theorem prime_pow_eq_seven {p e : ℕ} (hp : p.Prime) (he : e = 1 ∨ e = 2) (h : p ^ e = 7) :
    p = 7 ∧ e = 1 := by
  rcases he with rfl | rfl
  · exact ⟨by simpa using h, rfl⟩
  · exfalso
    have : p ≤ 2 := by nlinarith
    have := hp.two_le
    have : p = 2 := by omega
    subst this
    omega

namespace E22TwoAlt

variable {X : Type} [Group X] {D A O : Prop}

theorem of_card_168 (h : E22TwoAlt X D A O)
    (hN : Nat.card X = 168) : (IsPSL 3 2 1 X ∧ D) ∨ (IsPSL 2 7 1 X ∧ A) := by
  have hS : SmallOrder (Nat.card X) := Or.inl hN
  rcases h with ⟨n, hn2, hB⟩ | ⟨n, hn, hX, hD⟩ | ⟨p, e, hp, hp3, he, -, hX, hA⟩ |
      ⟨p, hp, hp2, hX | hX⟩
  · exfalso
    rcases hB with hX | hX | hX
    · rcases psl_two_small hX hS with h7 | h9
      · exact (two_pow_ne (by omega)).1 h7
      · exact (two_pow_ne (by omega)).2 h9
    · exact sz_small hn2 hX hS
    · exact psu_three_two_small hn2 hX hS
  · rcases hX with hX | hX
    · obtain ⟨rfl, -⟩ := psl_three_two_small hn hX hS
      exact Or.inl ⟨hX, hD⟩
    · obtain ⟨-, -, hc⟩ := sp4Prime_small hn hX hS
      omega
  · rcases psl_two_small hX hS with h7 | h9
    · obtain ⟨rfl, rfl⟩ := prime_pow_eq_seven hp he h7
      exact Or.inr ⟨hX, hA⟩
    · exact absurd h9 (prime_pow_ne_nine hp hp3 he)
  · obtain ⟨hp1, hX⟩ := hX
    have := psu_three_odd_small hp2 hX hS
    omega
  · exact (psl_three_odd_small hp2 hX.2.1 hS).elim

theorem of_card_360 (h : E22TwoAlt X D A O)
    (hN : Nat.card X = 360) : IsAlt 6 X ∧ D := by
  have hS : SmallOrder (Nat.card X) := Or.inr (Or.inl hN)
  rcases h with ⟨n, hn2, hB⟩ | ⟨n, hn, hX, hD⟩ | ⟨p, e, hp, hp3, he, -, hX, hA⟩ |
      ⟨p, hp, hp2, hX | hX⟩
  · exfalso
    rcases hB with hX | hX | hX
    · rcases psl_two_small hX hS with h7 | h9
      · exact (two_pow_ne (by omega)).1 h7
      · exact (two_pow_ne (by omega)).2 h9
    · exact sz_small hn2 hX hS
    · exact psu_three_two_small hn2 hX hS
  · rcases hX with hX | hX
    · obtain ⟨-, hc⟩ := psl_three_two_small hn hX hS
      omega
    · obtain ⟨-, hA6, -⟩ := sp4Prime_small hn hX hS
      exact ⟨hA6, hD⟩
  · exfalso
    rcases psl_two_small hX hS with h7 | h9
    · obtain ⟨rfl, rfl⟩ := prime_pow_eq_seven hp he h7
      have h1 := B69.card_psl_two_mul hX
      norm_num [hN] at h1
    · exact prime_pow_ne_nine hp hp3 he h9
  · exfalso
    obtain ⟨hp1, hX⟩ := hX
    have := psu_three_odd_small hp2 hX hS
    omega
  · exact (psl_three_odd_small hp2 hX.2.1 hS).elim

theorem false_of_card_2520 (h : E22TwoAlt X D A O)
    (hN : Nat.card X = 2520) : False := by
  have hS : SmallOrder (Nat.card X) := Or.inr (Or.inr (Or.inl hN))
  rcases h with ⟨n, hn2, hB⟩ | ⟨n, hn, hX, hD⟩ | ⟨p, e, hp, hp3, he, -, hX, hA⟩ |
      ⟨p, hp, hp2, hX | hX⟩
  · rcases hB with hX | hX | hX
    · rcases psl_two_small hX hS with h7 | h9
      · exact (two_pow_ne (by omega)).1 h7
      · exact (two_pow_ne (by omega)).2 h9
    · exact sz_small hn2 hX hS
    · exact psu_three_two_small hn2 hX hS
  · rcases hX with hX | hX
    · obtain ⟨-, hc⟩ := psl_three_two_small hn hX hS
      omega
    · obtain ⟨-, -, hc⟩ := sp4Prime_small hn hX hS
      omega
  · rcases psl_two_small hX hS with h7 | h9
    · obtain ⟨rfl, rfl⟩ := prime_pow_eq_seven hp he h7
      have h1 := B69.card_psl_two_mul hX
      norm_num [hN] at h1
    · exact prime_pow_ne_nine hp hp3 he h9
  · obtain ⟨hp1, hX⟩ := hX
    have := psu_three_odd_small hp2 hX hS
    omega
  · exact (psl_three_odd_small hp2 hX.2.1 hS).elim

theorem false_of_card_6048 (h : E22TwoAlt X D A O)
    (hN : Nat.card X = 6048) : False := by
  have hS : SmallOrder (Nat.card X) := Or.inr (Or.inr (Or.inr hN))
  rcases h with ⟨n, hn2, hB⟩ | ⟨n, hn, hX, hD⟩ | ⟨p, e, hp, hp3, he, -, hX, hA⟩ |
      ⟨p, hp, hp2, hX | hX⟩
  · rcases hB with hX | hX | hX
    · rcases psl_two_small hX hS with h7 | h9
      · exact (two_pow_ne (by omega)).1 h7
      · exact (two_pow_ne (by omega)).2 h9
    · exact sz_small hn2 hX hS
    · exact psu_three_two_small hn2 hX hS
  · rcases hX with hX | hX
    · obtain ⟨-, hc⟩ := psl_three_two_small hn hX hS
      omega
    · obtain ⟨-, -, hc⟩ := sp4Prime_small hn hX hS
      omega
  · rcases psl_two_small hX hS with h7 | h9
    · obtain ⟨rfl, rfl⟩ := prime_pow_eq_seven hp he h7
      have h1 := B69.card_psl_two_mul hX
      norm_num [hN] at h1
    · exact prime_pow_ne_nine hp hp3 he h9
  · obtain ⟨hp1, hX⟩ := hX
    have := psu_three_odd_small hp2 hX hS
    omega
  · exact (psl_three_odd_small hp2 hX.2.1 hS).elim

end E22TwoAlt

end Lem1227Eq

end CFSG.Quasithin.H13
