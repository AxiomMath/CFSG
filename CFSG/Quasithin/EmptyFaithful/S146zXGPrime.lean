module

public import CFSG.Quasithin.EmptyFaithful.S146zXGIdent
public import CFSG.Quasithin.EmptyFaithful.S146zXGOrder
public import CFSG.Quasithin.Background.F918P2

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem eq_two_of_psl_orders {q n : ℕ} (hqp : q.Prime) (hq2 : q ≠ 2) (hn : 2 ≤ n)
    (h : q * (q ^ 2 - 1) = 2 * (2 ^ n * ((2 ^ n) ^ 2 - 1))) : n = 2 := by
  have hq3 : 3 ≤ q := by have := hqp.two_le; omega
  have ht4 : 4 ≤ 2 ^ n := CFSG.Quasithin.GoldS146R.four_le_two_pow hn
  generalize ht : 2 ^ n = t at h ht4
  have hcop2 : Nat.Coprime q 2 := (Nat.coprime_primes hqp Nat.prime_two).mpr hq2
  have hcopt : Nat.Coprime q t := by
    rw [← ht]
    exact Nat.Coprime.pow_right n hcop2
  have hd1 : q ∣ 2 * (t * (t ^ 2 - 1)) := ⟨q ^ 2 - 1, by rw [← h]⟩
  have hd2 : q ∣ t * (t ^ 2 - 1) := hcop2.dvd_of_dvd_mul_left hd1
  have hd3 : q ∣ t ^ 2 - 1 := hcopt.dvd_of_dvd_mul_left hd2
  have hfac : t ^ 2 - 1 = (t + 1) * (t - 1) := by
    have := Nat.sq_sub_sq t 1
    simpa using this
  have hqle : q ≤ t + 1 := by
    rw [hfac] at hd3
    rcases (Nat.Prime.dvd_mul hqp).mp hd3 with h1 | h1
    · exact Nat.le_of_dvd (by omega) h1
    · have := Nat.le_of_dvd (by omega) h1
      omega
  by_contra hne
  have hn3 : 3 ≤ n := by omega
  have ht8 : 8 ≤ t := by
    rw [← ht]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have ht1 : 1 ≤ t ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [hq1, ht1] at h
  have hqle' : (q : ℤ) ≤ t + 1 := by exact_mod_cast hqle
  have hq3' : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  have ht8' : (8 : ℤ) ≤ t := by exact_mod_cast ht8
  have hP : (0 : ℤ) ≤ ((t : ℤ) + 1) ^ 2 + ((t : ℤ) + 1) * q + (q : ℤ) ^ 2 - 1 := by nlinarith
  have hmono := mul_nonneg (sub_nonneg.mpr hqle') hP
  have hpos : (0 : ℤ) < (t : ℤ) * ((t : ℤ) - 4) * ((t : ℤ) + 1) := by
    have h1 : (0 : ℤ) < t := by linarith
    have h2 : (0 : ℤ) < (t : ℤ) - 4 := by linarith
    have h3 : (0 : ℤ) < (t : ℤ) + 1 := by linarith
    exact mul_pos (mul_pos h1 h2) h3
  nlinarith

theorem listI_of_psl2_prime {p : ℕ} (hp : p = 3 ∨ p = 5) {X : Type} [Group X]
    {q : ℕ} (hqp : q.Prime) (hq2 : q ≠ 2) (hmod : StatedClassicalModel X StatedLieTag.PSL 2 q 1)
    (hshape : FiveShape X) (hdvd : p ∣ Nat.card X) :
    ListI p X ∨ (p = 5 ∧ Nat.card X = 60) := by
  have hqodd : Odd q := hqp.odd_of_ne_two hq2
  have hmod' : IsPSL 2 q 1 X := hmod
  rcases hshape with ⟨n, hn⟩ | ⟨n, hn⟩ | hA5 | hL3
  · have hn2 : 2 ≤ n := two_le_of_psl_two_two hn
    have h1 : q * (q ^ 2 - 1) = 2 * (2 ^ n * ((2 ^ n) ^ 2 - 1)) := by
      rw [← card_isPSL_two_even hn, ← two_mul_card_isPSL_two_odd hqodd hmod']
    obtain rfl : n = 2 := eq_two_of_psl_orders hqp hq2 hn2 h1
    have hc : Nat.card X = 60 := by rw [card_isPSL_two_even hn]; norm_num
    rcases hp with rfl | rfl
    · exact Or.inl (listI_of_psl2_even Nat.prime_three hn (by norm_num))
    · exact Or.inr ⟨rfl, hc⟩
  · exact absurd (three_dvd_card_isPSL_two_odd hqodd hmod') (not_three_dvd_card_isSz hn)
  · rcases hp with rfl | rfl
    · obtain ⟨e⟩ := hA5
      obtain ⟨e5⟩ := nonempty_mulEquiv_sl_two_four_of_alt_five
      exact Or.inl (Or.inl ⟨2, le_rfl, by norm_num, ⟨e.trans e5.symm⟩⟩)
    · exact Or.inr ⟨rfl, card_isAlt_five hA5⟩
  · rcases hp with rfl | rfl
    · exact Or.inl (Or.inr ⟨rfl, nonempty_mulEquiv_sl_three_zmod_two hL3⟩)
    · rw [card_isPSL_three_two hL3] at hdvd
      exact absurd hdvd (by norm_num)

end CFSG.Quasithin.S146zX
