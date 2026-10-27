module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.Open CFSG.Blueprint C11P9B

theorem eq_five_one_of_pow_eq_five {p e : ℕ} (hp : p.Prime) (h : p ^ e = 5) :
    p = 5 ∧ e = 1 := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at h
  have hp5 : p = 5 := by
    have h5 : p ∣ 5 := by
      rw [← h]
      exact dvd_pow_self p he
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5
  subst hp5
  exact ⟨rfl, Nat.pow_right_injective (by norm_num) (h.trans (by norm_num))⟩

theorem eq_U35_of_window {X : Type} [Group X] {N aL bL aU bU : ℕ} (hN : Nat.card X = N)
    (haL : aL ^ 3 * ((aL ^ 2 - 1) * (aL ^ 3 - 1)) < N)
    (hbL : 3 * N < (bL + 1) ^ 3 * (((bL + 1) ^ 2 - 1) * ((bL + 1) ^ 3 - 1)))
    (hL : ∀ q < bL + 1, aL < q →
      N * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))
    (haU : aU ^ 3 * ((aU ^ 2 - 1) * (aU ^ 3 + 1)) < N)
    (hbU : 3 * N < (bU + 1) ^ 3 * (((bU + 1) ^ 2 - 1) * ((bU + 1) ^ 3 + 1)))
    (hU : ∀ q < bU + 1, aU < q → q ≠ 5 →
      N * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)))
    {s : Bool} {p e : ℕ} (hp : p.Prime) (h : IsPSLEps3 s p e X) :
    s = false ∧ p = 5 ∧ e = 1 := by
  cases s
  · have hc := card_mul_gcd_of_isPSU3 (X := X) h
    rw [hN] at hc
    have hd1 : 1 ≤ Nat.gcd 3 (p ^ e + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hd3 : Nat.gcd 3 (p ^ e + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    obtain ⟨h1, h2⟩ := window_U hd1 hd3 hc haU hbU
    by_cases h5 : p ^ e = 5
    · exact ⟨rfl, eq_five_one_of_pow_eq_five hp h5⟩
    · exact absurd hc (hU _ (by omega) h1 h5)
  · have hc := card_mul_gcd_of_isPSL3' (X := X) h
    rw [hN] at hc
    have hd1 : 1 ≤ Nat.gcd 3 (p ^ e - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hd3 : Nat.gcd 3 (p ^ e - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    obtain ⟨h1, h2⟩ := window_L hd1 hd3 hc haL hbL
    exact absurd hc (hL _ (by omega) h1)

theorem psleps3_of_card_2520 {X : Type} [Group X] (hX : Nat.card X = 2520) {s : Bool}
    {p e : ℕ} (hp : p.Prime) (h : IsPSLEps3 s p e X) : s = false ∧ p = 5 ∧ e = 1 :=
  eq_U35_of_window (aL := 2) (bL := 3) (aU := 2) (bU := 3) hX (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num) (by decide) hp h

theorem psleps3_of_card_7560 {X : Type} [Group X] (hX : Nat.card X = 7560) {s : Bool}
    {p e : ℕ} (hp : p.Prime) (h : IsPSLEps3 s p e X) : s = false ∧ p = 5 ∧ e = 1 :=
  eq_U35_of_window (aL := 3) (bL := 3) (aU := 3) (bU := 3) hX (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num) (by decide) hp h

theorem psleps3_of_card_443520 {X : Type} [Group X] (hX : Nat.card X = 443520) {s : Bool}
    {p e : ℕ} (hp : p.Prime) (h : IsPSLEps3 s p e X) : s = false ∧ p = 5 ∧ e = 1 :=
  eq_U35_of_window (aL := 5) (bL := 5) (aU := 5) (bU := 5) hX (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num) (by decide) hp h

theorem psleps3_of_card_1330560 {X : Type} [Group X] (hX : Nat.card X = 1330560) {s : Bool}
    {p e : ℕ} (hp : p.Prime) (h : IsPSLEps3 s p e X) : s = false ∧ p = 5 ∧ e = 1 :=
  eq_U35_of_window (aL := 5) (bL := 6) (aU := 5) (bU := 6) hX (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num) (by decide) hp h

theorem psleps3_of_card_10200960 {X : Type} [Group X] (hX : Nat.card X = 10200960) {s : Bool}
    {p e : ℕ} (hp : p.Prime) (h : IsPSLEps3 s p e X) : s = false ∧ p = 5 ∧ e = 1 :=
  eq_U35_of_window (aL := 7) (bL := 8) (aU := 7) (bU := 8) hX (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num) (by decide) hp h

theorem psleps3_of_card_604800 {X : Type} [Group X] (hX : Nat.card X = 604800) {s : Bool}
    {p e : ℕ} (hp : p.Prime) (h : IsPSLEps3 s p e X) : s = false ∧ p = 5 ∧ e = 1 :=
  eq_U35_of_window (aL := 5) (bL := 6) (aU := 5) (bU := 6) hX (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num) (by decide) hp h

theorem psleps3_of_card_J4 {X : Type} [Group X] (hX : Nat.card X = 86775571046077562880)
    {s : Bool} {p e : ℕ} (hp : p.Prime) (h : IsPSLEps3 s p e X) : s = false ∧ p = 5 ∧ e = 1 :=
  eq_U35_of_window (aL := 310) (bL := 356) (aU := 310) (bU := 356) hX (by norm_num)
    (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel) hp h

theorem psleps3_of_card_44352000 {X : Type} [Group X] (hX : Nat.card X = 44352000) {s : Bool}
    {p e : ℕ} (hp : p.Prime) (h : IsPSLEps3 s p e X) : s = false ∧ p = 5 ∧ e = 1 :=
  eq_U35_of_window (aL := 9) (bL := 10) (aU := 9) (bU := 10) hX (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num) (by decide) hp h

theorem psleps3_of_card_145926144000 {X : Type} [Group X] (hX : Nat.card X = 145926144000)
    {s : Bool} {p e : ℕ} (hp : p.Prime) (h : IsPSLEps3 s p e X) : s = false ∧ p = 5 ∧ e = 1 :=
  eq_U35_of_window (aL := 24) (bL := 28) (aU := 24) (bU := 28) hX (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num) (by decide) hp h

theorem psleps3_of_card_378000 {X : Type} [Group X] (hX : Nat.card X = 378000) {s : Bool}
    {p e : ℕ} (hp : p.Prime) (h : IsPSLEps3 s p e X) : s = false ∧ p = 5 ∧ e = 1 :=
  eq_U35_of_window (aL := 5) (bL := 5) (aU := 4) (bU := 5) hX (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num) (by decide) hp h

theorem psleps3_of_card_126000 {X : Type} [Group X] (hX : Nat.card X = 126000) {s : Bool}
    {p e : ℕ} (hp : p.Prime) (h : IsPSLEps3 s p e X) : s = false ∧ p = 5 ∧ e = 1 :=
  eq_U35_of_window (aL := 4) (bL := 5) (aU := 4) (bU := 5) hX (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num) (by decide) hp h

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
