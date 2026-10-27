module

public import CFSG.Quasithin.Background.B69Num

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders
open scoped commutatorElement

namespace B69

theorem cubic_no_2520 (q g : ℕ) (hg : 0 < g) (hg2 : g ≤ 2) (h : 2520 * g + q = q ^ 3) : False := by
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | h0
    · simp at h
      omega
    · exact h0
  interval_cases g
  · have hq : q ≤ 14 := by
      by_contra hlt
      push Not at hlt
      nlinarith [Nat.mul_le_mul hlt.le hlt.le]
    interval_cases q <;> omega
  · have hq : q ≤ 17 := by
      by_contra hlt
      push Not at hlt
      nlinarith [Nat.mul_le_mul hlt.le hlt.le]
    interval_cases q <;> omega

theorem big_three_2520 {q g X : ℕ} (hq : 4 ≤ q) (hg : g ≤ 3)
    (h : X * g = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∨ X * g = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) :
    2520 < X := by
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
  have h6 : X * g ≤ 2520 * 3 := Nat.mul_le_mul hX hg
  rcases h with h | h <;> norm_num at h4 h5 h6 <;> omega

theorem big_four_2520 {q X : ℕ} (hq : 4 ≤ q) (h : X = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) :
    2520 < X := by
  have h1 : 4 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have h2 : 4 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
  have h3 : 4 ^ 4 - 1 ≤ q ^ 4 - 1 := Nat.sub_le_sub_right h1 1
  have h4 : 4 ^ 4 * ((4 ^ 2 - 1) * (4 ^ 4 - 1)) ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  rw [h]
  norm_num at h4
  omega

theorem no_cube_dvd_2520 {p : ℕ} (hp : 5 ≤ p) (hodd : p % 2 = 1) (h : p ^ 3 ∣ 2520) : False := by
  have hle : p ^ 3 ≤ 2520 := Nat.le_of_dvd (by norm_num) h
  have hp13 : p ≤ 13 := by
    by_contra hlt
    push Not at hlt
    have : 14 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hlt 3
    omega
  have key : ∀ q ∈ Finset.Icc 5 13, q % 2 = 1 → ¬ q ^ 3 ∣ 2520 := by decide +kernel
  exact key p (Finset.mem_Icc.2 ⟨hp, hp13⟩) hodd h

namespace E22Fam

theorem card_ne_2520 {F : Type} [Group F] (h : E22Fam F)
    (hN : Nat.card F = 2520) : False := by
  rcases h with ⟨p, e, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨p, hp, h⟩ | ⟨p, hp, h⟩
  · have h1 := card_psl_two_mul h
    have hg1 : 0 < Nat.gcd 2 (p ^ e - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hg2 : Nat.gcd 2 (p ^ e - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    rw [hN] at h1
    exact cubic_no_2520 (p ^ e) _ hg1 hg2 h1
  · obtain ⟨-, a, ha, F', _, _, hfa, hF, ⟨e⟩⟩ := h
    have hF' : Nat.card F' = 2 ^ (2 * a + 1) := by rw [hF, hfa]
    have hc : Nat.card F = CFSG.Open.ordSuzuki (2 ^ n) := by
      rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hF', hfa, CFSG.Open.ordSuzuki]
      exact Nat.mul_right_comm _ _ _
    have hodd : Odd n := ⟨a, by omega⟩
    have h3 : ¬ 3 ∣ CFSG.Open.ordSuzuki (2 ^ n) :=
      CFSG.QuasithinUnique.Fin257.not_three_dvd_suzuki hodd
    rw [← hc, hN] at h3
    omega
  · have h1 := card_psu_three_mul h
    have hn2 : 2 ≤ n := by
      obtain ⟨-, hf, -, h32⟩ := h.1
      by_contra hlt
      have : n = 1 := by omega
      subst this
      exact h32 (by norm_num)
    have hg : Nat.gcd 3 (2 ^ n + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have := big_three_2520 hq hg (Or.inl h1)
    omega
  · have h1 := card_psl_three_mul h
    have hg : Nat.gcd 3 (2 ^ n - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · interval_cases n
      · norm_num at h1
        omega
      · norm_num at h1
        omega
    · have hq : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := big_three_2520 hq hg (Or.inr h1)
      omega
  · unfold E2.IsSp4Prime at h
    split_ifs at h with h1
    · obtain ⟨e⟩ := h
      have hc : Nat.card F = 360 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      omega
    · have hc := card_psp_four h
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · exact h1 (by omega)
      · have hq : 4 ≤ 2 ^ n := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
        have := big_four_2520 hq hc
        omega
  · have hpp : p.Prime := h.1.1
    have h1 := card_psu_three_mul h
    rw [pow_one] at h1
    rcases Nat.lt_or_ge p 5 with hp5 | hp5
    · have hp3 : p = 3 := by
        have := hpp.two_le
        interval_cases p
        · exact absurd rfl hp
        · rfl
        · exact absurd hpp (by norm_num)
      subst hp3
      norm_num at h1
      omega
    · have hcop := coprime_pow_gcd hpp hp5 (Nat.gcd_dvd_left 3 (p + 1))
      have hd : p ^ 3 ∣ Nat.card F * Nat.gcd 3 (p + 1) := by
        rw [h1]; exact Dvd.intro _ rfl
      rw [hN] at hd
      exact no_cube_dvd_2520 hp5 (by have := hpp.eq_two_or_odd; omega)
        (by simpa [hN] using (hcop.dvd_of_dvd_mul_right (hN ▸ hd)))
  · have hpp : p.Prime := h.1.1
    have h1 := card_psl_three_mul h
    rw [pow_one] at h1
    rcases Nat.lt_or_ge p 5 with hp5 | hp5
    · have hp3 : p = 3 := by
        have := hpp.two_le
        interval_cases p
        · exact absurd rfl hp
        · rfl
        · exact absurd hpp (by norm_num)
      subst hp3
      norm_num at h1
      omega
    · have hcop := coprime_pow_gcd hpp hp5 (Nat.gcd_dvd_left 3 (p - 1))
      have hd : p ^ 3 ∣ Nat.card F * Nat.gcd 3 (p - 1) := by
        rw [h1]; exact Dvd.intro _ rfl
      rw [hN] at hd
      exact no_cube_dvd_2520 hp5 (by have := hpp.eq_two_or_odd; omega)
        (hcop.dvd_of_dvd_mul_right hd)

end E22Fam

end B69

end CFSG.Quasithin
