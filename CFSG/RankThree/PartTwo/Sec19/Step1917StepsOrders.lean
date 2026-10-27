module

public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.K72SLPiIdent

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus)

namespace Step1917Steps

theorem sl3Order_le {x y : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) ≤ y ^ 3 * (y ^ 2 - 1) * (y ^ 3 - 1) := by
  rcases Nat.eq_or_lt_of_le hxy with rfl | h
  · exact le_rfl
  · exact (KFacts.sl3Order_lt hx h).le

theorem su3Order_le {x y : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    x ^ 3 * (x ^ 2 - 1) * (x ^ 3 + 1) ≤ y ^ 3 * (y ^ 2 - 1) * (y ^ 3 + 1) := by
  rcases Nat.eq_or_lt_of_le hxy with rfl | h
  · exact le_rfl
  · exact (KFacts.su3Order_lt hx h).le

theorem sl3Order_ne_of_bracket {Q a N : ℕ} (hQ : 1 ≤ Q) (ha : 1 ≤ a)
    (h1 : a ^ 3 * (a ^ 2 - 1) * (a ^ 3 - 1) < N)
    (h2 : N < (a + 1) ^ 3 * ((a + 1) ^ 2 - 1) * ((a + 1) ^ 3 - 1)) :
    Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1) ≠ N := by
  intro h
  rcases le_or_gt Q a with hle | hlt
  · have h3 := (sl3Order_le hQ hle).trans_lt h1
    rw [h] at h3
    exact lt_irrefl N h3
  · have h3 := h2.trans_le (sl3Order_le (by omega) hlt)
    rw [h] at h3
    exact lt_irrefl N h3

theorem su3Order_ne_of_bracket {Q a N : ℕ} (hQ : 1 ≤ Q) (ha : 1 ≤ a)
    (h1 : a ^ 3 * (a ^ 2 - 1) * (a ^ 3 + 1) < N)
    (h2 : N < (a + 1) ^ 3 * ((a + 1) ^ 2 - 1) * ((a + 1) ^ 3 + 1)) :
    Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) ≠ N := by
  intro h
  rcases le_or_gt Q a with hle | hlt
  · have h3 := (su3Order_le hQ hle).trans_lt h1
    rw [h] at h3
    exact lt_irrefl N h3
  · have h3 := h2.trans_le (su3Order_le (by omega) hlt)
    rw [h] at h3
    exact lt_irrefl N h3

@[expose] def IsFixedOrder (n : ℕ) : Prop :=
  n = 25920 ∨ n = 34693789777920 ∨ n = 987033600 ∨ n = 9999360 ∨ n = 20158709760 ∨
    n = 163849992929280 ∨ n = 1451520 ∨ n = 197406720 ∨ n = 1814400 ∨ n = 360 ∨ n = 6048

theorem sl3Order_ne_of_isFixedOrder {Q n : ℕ} (hQ : 1 ≤ Q) (hn : IsFixedOrder n) :
    Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1) ≠ 3 * n := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sl3Order_ne_of_bracket (a := 4) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact sl3Order_ne_of_bracket (a := 56) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact sl3Order_ne_of_bracket (a := 15) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact sl3Order_ne_of_bracket (a := 8) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact sl3Order_ne_of_bracket (a := 22) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact sl3Order_ne_of_bracket (a := 68) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact sl3Order_ne_of_bracket (a := 6) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact sl3Order_ne_of_bracket (a := 12) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact sl3Order_ne_of_bracket (a := 6) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact sl3Order_ne_of_bracket (a := 2) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact sl3Order_ne_of_bracket (a := 3) hQ (by norm_num) (by norm_num) (by norm_num)

theorem su3Order_ne_of_isFixedOrder {Q n : ℕ} (hQ : 1 ≤ Q) (hn : IsFixedOrder n ∨ n = 20160) :
    Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) ≠ 3 * n := by
  rcases hn with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  · exact su3Order_ne_of_bracket (a := 4) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact su3Order_ne_of_bracket (a := 56) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact su3Order_ne_of_bracket (a := 15) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact su3Order_ne_of_bracket (a := 8) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact su3Order_ne_of_bracket (a := 22) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact su3Order_ne_of_bracket (a := 68) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact su3Order_ne_of_bracket (a := 6) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact su3Order_ne_of_bracket (a := 12) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact su3Order_ne_of_bracket (a := 6) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact su3Order_ne_of_bracket (a := 2) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact su3Order_ne_of_bracket (a := 3) hQ (by norm_num) (by norm_num) (by norm_num)
  · exact su3Order_ne_of_bracket (a := 3) hQ (by norm_num) (by norm_num) (by norm_num)

theorem eq_four_of_sl3Order_eq {Q : ℕ} (hQ : 1 ≤ Q)
    (h : Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1) = 3 * 20160) : Q = 4 := by
  rcases Nat.lt_or_ge Q 4 with h4 | h4
  · have := sl3Order_le hQ (show Q ≤ 3 by omega)
    norm_num at this
    omega
  · rcases Nat.eq_or_lt_of_le h4 with h4 | h5
    · exact h4.symm
    · have := sl3Order_le (by norm_num) (show 5 ≤ Q by omega)
      norm_num at this
      omega

theorem two_pow_le_of_dvd {u v N : ℕ} (hu0 : 0 < u) (hv0 : 0 < v) (hu : 2 ∣ u) (hv : 2 ∣ v)
    (huv : u + 2 = v ∨ v + 2 = u) (hdvd : 2 ^ N ∣ u ^ 2 * v) :
    2 ^ (N - 2) ≤ v ∨ 2 ^ (N / 2) ≤ u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hval := (padicValNat_dvd_iff_le (p := 2) (by positivity : u ^ 2 * v ≠ 0)).mp hdvd
  rw [padicValNat.mul (by positivity) hv0.ne', padicValNat.pow] at hval
  have h4 : ¬ 4 ∣ u ∨ ¬ 4 ∣ v := by
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    rcases huv with h | h <;> omega
  rcases h4 with h4 | h4
  · have hu1 : padicValNat 2 u ≤ 1 := by
      by_contra h
      apply h4
      have h' := (padicValNat_dvd_iff_le (p := 2) (n := 2) hu0.ne').mpr (by omega)
      simpa using h'
    left
    exact Nat.le_of_dvd hv0 ((padicValNat_dvd_iff_le (p := 2) hv0.ne').mpr (by omega))
  · have hv1 : padicValNat 2 v ≤ 1 := by
      by_contra h
      apply h4
      have h' := (padicValNat_dvd_iff_le (p := 2) (n := 2) hv0.ne').mpr (by omega)
      simpa using h'
    right
    exact Nat.le_of_dvd hu0 ((padicValNat_dvd_iff_le (p := 2) hu0.ne').mpr (by omega))


theorem sl3Order_factor' {Q : ℕ} (hQ : 1 ≤ Q) :
    Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1) = Q ^ 3 * (Q ^ 2 + Q + 1) * ((Q - 1) ^ 2 * (Q + 1)) := by
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ hQ
  zify [hQ, h2, h3]
  ring

theorem su3Order_factor' {Q : ℕ} (hQ : 1 ≤ Q) :
    Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) = Q ^ 3 * (Q ^ 2 - Q + 1) * ((Q + 1) ^ 2 * (Q - 1)) := by
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ
  have hQ2 : Q ≤ Q ^ 2 := by nlinarith
  zify [hQ, h2, hQ2]
  ring

theorem two_pow_le_of_dvd_sl3Order {Q N : ℕ} (hQ : Odd Q) (hQ3 : 3 ≤ Q) (hN : 4 ≤ N)
    (h : (2 ^ N ∣ Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1)) ∨
      (2 ^ N ∣ Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1))) :
    2 ^ (N / 2) ≤ Q + 1 := by
  have hQ1 : 1 ≤ Q := by omega
  obtain ⟨k, rfl⟩ := hQ
  have hodd : ∀ w : ℕ, Odd w → Nat.Coprime (2 ^ N) (((2 * k + 1) ^ 3) * w) := fun w hw =>
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ((Odd.pow ⟨k, rfl⟩).mul hw))
  have hmono : 2 ^ (N / 2) ≤ 2 ^ (N - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases h with h | h
  · rw [sl3Order_factor' hQ1] at h
    have hw : Odd ((2 * k + 1) ^ 2 + (2 * k + 1) + 1) := ⟨2 * k ^ 2 + 3 * k + 1, by ring⟩
    have h' := (hodd _ hw).dvd_of_dvd_mul_left h
    rcases two_pow_le_of_dvd (u := 2 * k + 1 - 1) (v := 2 * k + 1 + 1) (by omega) (by omega)
      ⟨k, by omega⟩ ⟨k + 1, by omega⟩ (Or.inl (by omega)) h' with h1 | h1
    · exact hmono.trans h1
    · omega
  · rw [su3Order_factor' hQ1] at h
    have hw : Odd ((2 * k + 1) ^ 2 - (2 * k + 1) + 1) := by
      refine ⟨2 * k ^ 2 + k, ?_⟩
      have : 2 * k + 1 ≤ (2 * k + 1) ^ 2 := by nlinarith
      zify [this]
      ring
    have h' := (hodd _ hw).dvd_of_dvd_mul_left h
    rcases two_pow_le_of_dvd (u := 2 * k + 1 + 1) (v := 2 * k + 1 - 1) (by omega) (by omega)
      ⟨k + 1, by omega⟩ ⟨k, by omega⟩ (Or.inr (by omega)) h' with h1 | h1
    · exact hmono.trans (h1.trans (by omega))
    · exact h1

theorem odd_of_two_pow_mod_three {e : ℕ} (h : 2 ^ e % 3 = 2) : Odd e := by
  rcases Nat.even_or_odd e with ⟨k, rfl⟩ | ho
  · exfalso
    rw [show k + k = 2 * k by ring, pow_mul, Nat.pow_mod] at h
    norm_num at h
  · exact ho

theorem su3Order_two_pow_ne {e m a : ℕ} (he : Odd e) {r : ℕ} (hr : Odd r)
    (ha : a = 4 ∨ a = 6) :
    (2 ^ e) ^ 3 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1) ≠ 2 ^ (m * a) * r := by
  intro h
  have he1 : 0 < e := he.pos
  have hodd : Odd (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1)) :=
    (Timmesfeld.Orders.odd_pow_sub_one he1 two_pos).mul
      (Timmesfeld.Orders.odd_pow_add_one he1 three_pos)
  have h' : 2 ^ (e * 3) * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1)) = 2 ^ (m * a) * r := by
    rw [pow_mul, ← mul_assoc]
    exact h
  have := Timmesfeld.Orders.eq_of_two_pow_mul_odd hodd hr h'
  obtain ⟨j, rfl⟩ := he
  rcases ha with rfl | rfl <;> omega


theorem pow_three_dvd_of_coprime {Q N s : ℕ} (hQ : Odd Q) (hQ3 : ¬ 3 ∣ Q)
    (h : Q ^ 3 ∣ 3 * (2 ^ N * s)) : Q ^ 3 ∣ s := by
  have h3 : Nat.Coprime (Q ^ 3) 3 :=
    Nat.Coprime.pow_left _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_three).mpr hQ3)))
  have h2 : Nat.Coprime (Q ^ 3) (2 ^ N) :=
    Nat.Coprime.pow _ _ (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr hQ))
  exact (h2.dvd_of_dvd_mul_left (h3.dvd_of_dvd_mul_left h))

theorem false_of_sl3Order_eq_sp4 {Q m : ℕ} (hQ : Odd Q) (hQ5 : 5 ≤ Q) (hQ3 : ¬ 3 ∣ Q)
    (hm : 1 ≤ m)
    (h : Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1) =
        3 * (2 ^ (m * 4) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1))) ∨
      Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) =
        3 * (2 ^ (m * 4) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)))) : False := by
  set x := 2 ^ m with hx
  set s := (x ^ 2 - 1) * (x ^ 4 - 1) with hs
  have hx2 : 2 ≤ x := by
    rw [hx]
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
  have hdvd : (2 ^ (m * 4) ∣ Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1)) ∨
      (2 ^ (m * 4) ∣ Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1)) := by
    rcases h with h | h
    · exact Or.inl ⟨3 * s, by rw [h]; ring⟩
    · exact Or.inr ⟨3 * s, by rw [h]; ring⟩
  have hle := two_pow_le_of_dvd_sl3Order hQ (by omega) (by omega) hdvd
  rw [show m * 4 / 2 = m * 2 by omega, pow_mul] at hle
  rw [← hx] at hle
  have hQs : Q ^ 3 ∣ s := by
    refine pow_three_dvd_of_coprime (N := m * 4) hQ hQ3 ?_
    rcases h with h | h
    · rw [← h, mul_assoc]
      exact Dvd.intro _ rfl
    · rw [← h, mul_assoc]
      exact Dvd.intro _ rfl
  have hs0 : 0 < s := by
    have h1 : 1 < x ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    have h2 : 1 < x ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
    exact Nat.mul_pos (by omega) (by omega)
  have hslt : s < (x ^ 2) ^ 3 := by
    have h1 : x ^ 2 - 1 < x ^ 2 := Nat.sub_lt (by positivity) one_pos
    have h2 : x ^ 4 - 1 ≤ x ^ 4 := Nat.sub_le _ _
    calc s < x ^ 2 * x ^ 4 := Nat.mul_lt_mul_of_lt_of_le h1 h2 (by positivity)
      _ = (x ^ 2) ^ 3 := by ring
  have hQx : Q < x ^ 2 := by
    by_contra hge
    push Not at hge
    have := Nat.pow_le_pow_left hge 3
    have := Nat.le_of_dvd hs0 hQs
    omega
  have hQ1 : x ^ 2 = Q + 1 := by omega
  have hs' : s = Q ^ 2 * (Q + 2) := by
    have h4 : x ^ 4 = (Q + 1) ^ 2 := by rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hQ1]
    have e : (Q + 1) ^ 2 = Q * (Q + 2) + 1 := by ring
    rw [hs, hQ1, h4, e, Nat.add_sub_cancel, Nat.add_sub_cancel]
    ring
  rw [hs', show Q ^ 3 = Q ^ 2 * Q by ring] at hQs
  have hQ2 : Q ∣ Q + 2 := Nat.dvd_of_mul_dvd_mul_left (by positivity) hQs
  have : Q ∣ 2 := (Nat.dvd_add_right (dvd_refl Q)).mp hQ2
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem pow_eight_le_cube {x : ℕ} (hx : 2 ≤ x) : x ^ 8 ≤ (x ^ 3 - 1) ^ 3 := by
  have h3 : 8 ≤ x ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
  set y := x ^ 3 - 1 with hy
  have hxy : x ^ 3 = y + 1 := by omega
  have hy7 : 7 ≤ y := by omega
  have h9 : 2 * x ^ 8 ≤ x ^ 9 := by
    calc 2 * x ^ 8 ≤ x * x ^ 8 := Nat.mul_le_mul_right _ hx
      _ = x ^ 9 := by ring
  have h9' : x ^ 9 = (y + 1) ^ 3 := by rw [← hxy]; ring
  have hcube : (y + 1) ^ 3 ≤ 2 * y ^ 3 := by
    have e : (y + 1) ^ 3 = y ^ 3 + 3 * y ^ 2 + 3 * y + 1 := by ring
    have h1 : 7 * y ^ 2 ≤ y ^ 3 := by
      calc 7 * y ^ 2 ≤ y * y ^ 2 := Nat.mul_le_mul_right _ hy7
        _ = y ^ 3 := by ring
    have h2 : y ≤ y ^ 2 := by nlinarith
    have h3 : 1 ≤ y ^ 2 := by nlinarith
    rw [e]
    linarith
  linarith

theorem false_of_sl3Order_eq_g2 {Q m : ℕ} (hQ : Odd Q) (hQ5 : 5 ≤ Q) (hQ3 : ¬ 3 ∣ Q)
    (hm : 1 ≤ m)
    (h : Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1) =
        3 * (2 ^ (m * 6) * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1))) ∨
      Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) =
        3 * (2 ^ (m * 6) * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)))) : False := by
  set x := 2 ^ m with hx
  set s := (x ^ 6 - 1) * (x ^ 2 - 1) with hs
  have hx2 : 2 ≤ x := by
    rw [hx]
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
  have hdvd : (2 ^ (m * 6) ∣ Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1)) ∨
      (2 ^ (m * 6) ∣ Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1)) := by
    rcases h with h | h
    · exact Or.inl ⟨3 * s, by rw [h]; ring⟩
    · exact Or.inr ⟨3 * s, by rw [h]; ring⟩
  have hle := two_pow_le_of_dvd_sl3Order hQ (by omega) (by omega) hdvd
  rw [show m * 6 / 2 = m * 3 by omega, pow_mul] at hle
  rw [← hx] at hle
  have hQs : Q ^ 3 ∣ s := by
    refine pow_three_dvd_of_coprime (N := m * 6) hQ hQ3 ?_
    rcases h with h | h
    · rw [← h, mul_assoc]
      exact Dvd.intro _ rfl
    · rw [← h, mul_assoc]
      exact Dvd.intro _ rfl
  have hs0 : 0 < s := by
    have h1 : 1 < x ^ 6 := Nat.one_lt_pow (by norm_num) (by omega)
    have h2 : 1 < x ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    exact Nat.mul_pos (by omega) (by omega)
  have hslt : s < x ^ 8 := by
    have h1 : x ^ 6 - 1 < x ^ 6 := Nat.sub_lt (by positivity) one_pos
    have h2 : x ^ 2 - 1 ≤ x ^ 2 := Nat.sub_le _ _
    calc s < x ^ 6 * x ^ 2 := Nat.mul_lt_mul_of_lt_of_le h1 h2 (by positivity)
      _ = x ^ 8 := by ring
  have h8 := pow_eight_le_cube hx2
  have hcube : (x ^ 3 - 1) ^ 3 ≤ Q ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have := Nat.le_of_dvd hs0 hQs
  omega


theorem sp4Order_ne_m12 {m : ℕ} (hm : 1 ≤ m) :
    2 ^ (m * 4) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) ≠ 95040 := by
  rcases Nat.eq_or_lt_of_le hm with rfl | hm2
  · norm_num
  · have hx : 4 ≤ 2 ^ m := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm2)
    have h1 : 15 ≤ (2 ^ m) ^ 2 - 1 := by
      have := Nat.pow_le_pow_left hx 2
      omega
    have h2 : 255 ≤ (2 ^ m) ^ 4 - 1 := by
      have := Nat.pow_le_pow_left hx 4
      omega
    have h3 : 256 ≤ 2 ^ (m * 4) := by
      rw [pow_mul]
      exact le_trans (by norm_num) (Nat.pow_le_pow_left hx 4)
    have := Nat.mul_le_mul h3 (Nat.mul_le_mul h1 h2)
    omega

theorem g2Order_ne_m12 {m : ℕ} (hm : 1 ≤ m) :
    2 ^ (m * 6) * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) ≠ 95040 := by
  rcases Nat.eq_or_lt_of_le hm with rfl | hm2
  · norm_num
  · have hx : 4 ≤ 2 ^ m := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm2)
    have h1 : 4095 ≤ (2 ^ m) ^ 6 - 1 := by
      have := Nat.pow_le_pow_left hx 6
      omega
    have h2 : 15 ≤ (2 ^ m) ^ 2 - 1 := by
      have := Nat.pow_le_pow_left hx 2
      omega
    have h3 : 4096 ≤ 2 ^ (m * 6) := by
      rw [pow_mul]
      exact le_trans (by norm_num) (Nat.pow_le_pow_left hx 6)
    have := Nat.mul_le_mul h3 (Nat.mul_le_mul h1 h2)
    omega

theorem not_isFixedOrder_m12 : ¬ IsFixedOrder 95040 ∧ (95040 : ℕ) ≠ 20160 := by
  refine ⟨?_, by norm_num⟩
  unfold IsFixedOrder
  norm_num

theorem three_mul_card_of_isoLThreePi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : Sec4.IsoLThreePi X p e) :
    (p ^ e % 3 = 1 ∧ (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1) = 3 * Nat.card X ∧
        Nonempty (X ≃* projSL 3 (GaloisField p e))) ∨
      (p ^ e % 3 = 2 ∧ (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1) = 3 * Nat.card X) := by
  rcases h with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · left
    refine ⟨hq, ?_, ⟨φ⟩⟩
    have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
    rw [GaloisField.card p e (by omega), ← Nat.card_congr φ.toEquiv] at hc
    have hg : Nat.gcd 3 (p ^ e - 1) = 3 := Nat.gcd_eq_left (by omega)
    rw [hg] at hc
    rw [mul_assoc, ← hc, mul_comm]
  · right
    refine ⟨hq, ?_⟩
    have hc := KFacts.KS14.card_projSU_three_mul_gcd p e he
    rw [← Nat.card_congr φ.toEquiv] at hc
    have hg : Nat.gcd 3 (p ^ e + 1) = 3 := Nat.gcd_eq_left (by omega)
    rw [hg] at hc
    rw [mul_assoc, ← hc, mul_comm]

theorem card_cases_of_isList194
    {X : Type} [Group X]
    (hX : IsList194 X ∨ IsSmall194 X) :
    (∃ n : ℕ, 1 ≤ n ∧ (Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
        Nonempty (X ≃* projSL 3 (GaloisField 2 n)))) ∨
      (∃ m : ℕ, 1 ≤ m ∧
        Nat.card X = 2 ^ (m * 4) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1))) ∨
      (∃ m : ℕ, 1 ≤ m ∧
        Nat.card X = 2 ^ (m * 6) * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1))) ∨
      IsFixedOrder (Nat.card X) ∨ Nat.card X = 20160 := by
  rcases hX with
    (⟨n, hn, h | h | h | hG2⟩ | h | h | h | h | h | h | h | h | ⟨b, c, hbc, h⟩ | h) | hsmall
  · exact Or.inl ⟨n, hn, Or.inl h⟩
  · exact Or.inl ⟨n, hn, Or.inr h⟩
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inl ⟨n, hn, by rw [Nat.card_congr e.toEquiv,
      Step1911Proof.card_projSp_two hn]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, hn, by rw [Step1911Proof.card_isoGTwoEven hG2,
      Timmesfeld.Orders.ordG2_eq]⟩))
  · obtain ⟨e⟩ := h
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSU_four le_rfl]
    unfold IsFixedOrder
    norm_num
  · obtain ⟨e⟩ := h
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSU_four (by norm_num)]
    unfold IsFixedOrder
    norm_num
  · obtain ⟨e⟩ := h
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSL (by norm_num) le_rfl]
    decide
  · obtain ⟨e⟩ := h
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSL (by norm_num) (by norm_num),
      show CFSG.Open.ordA (4 - 1) (2 ^ 2) = 987033600 by decide]
    unfold IsFixedOrder
    norm_num
  · obtain ⟨e⟩ := h
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSL (by norm_num) le_rfl,
      show CFSG.Open.ordA (5 - 1) (2 ^ 1) = 9999360 by decide]
    unfold IsFixedOrder
    norm_num
  · obtain ⟨e⟩ := h
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSL (by norm_num) le_rfl,
      show CFSG.Open.ordA (6 - 1) (2 ^ 1) = 20158709760 by decide]
    unfold IsFixedOrder
    norm_num
  · obtain ⟨e⟩ := h
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSL (by norm_num) le_rfl,
      show CFSG.Open.ordA (7 - 1) (2 ^ 1) = 163849992929280 by decide]
    unfold IsFixedOrder
    norm_num
  · obtain ⟨e⟩ := h
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSp 3 le_rfl,
      show (2 ^ 1) ^ (3 ^ 2) * ∏ j ∈ Finset.Icc 1 3, ((2 ^ 1) ^ (2 * j) - 1) = 1451520 by
        decide]
    unfold IsFixedOrder
    norm_num
  · obtain ⟨e⟩ := h
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projOmegaMinus hbc,
      show CFSG.Open.ordTwistedD 4 (2 ^ 1) = 197406720 by decide]
    unfold IsFixedOrder
    norm_num
  · obtain ⟨e⟩ := h
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin,
      show Nat.factorial 10 / 2 = 1814400 by decide]
    unfold IsFixedOrder
    norm_num
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    unfold IsFixedOrder
    rcases Step1911Proof.card_of_isSmall194 hsmall with h | h <;> rw [h] <;> norm_num

theorem kStar_of_source
    {X : Type} [Group X]
    (hsrc : (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi X p e) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hX : IsList194 X ∨ IsSmall194 X) :
    (∃ n : ℕ, 1 ≤ n ∧ (Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
        Nonempty (X ≃* projSL 3 (GaloisField 2 n)))) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 10)) := by
  have hA10 : IsEmpty (X ≃* alternatingGroup (Fin 10)) := by
    refine ⟨fun φ => ?_⟩
    have hcard : Nat.card X = 1814400 := by
      rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    have hfix : IsFixedOrder (Nat.card X) := by
      rw [hcard]
      unfold IsFixedOrder
      norm_num
    rcases hsrc with ⟨p, e, hp, he, hiso⟩ | ⟨⟨ψ⟩⟩
    · have hQ : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.out.pos
      rcases three_mul_card_of_isoLThreePi he hiso with ⟨-, hf, -⟩ | ⟨-, hf⟩
      · exact sl3Order_ne_of_isFixedOrder hQ hfix hf
      · exact su3Order_ne_of_isFixedOrder hQ (Or.inl hfix) hf
    · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeM12] at hcard
      norm_num at hcard
  refine ⟨?_, hA10⟩
  rcases hsrc with ⟨p, e, hp, he, hiso⟩ | ⟨⟨ψ⟩⟩
  · have hpp : p.Prime := hp.out
    have hQ1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ hpp.pos
    by_cases hp2 : p = 2
    · subst hp2
      rcases hiso with ⟨-, hφ⟩ | ⟨hq, ⟨φ⟩⟩
      ·
        exact ⟨e, he, Or.inr hφ⟩
      ·
        have heo := odd_of_two_pow_mod_three hq
        have hf : (2 ^ e) ^ 3 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1) = 3 * Nat.card X := by
          rcases three_mul_card_of_isoLThreePi he (Or.inr ⟨hq, ⟨φ⟩⟩) with ⟨hq', -, -⟩ | ⟨-, hf⟩
          · omega
          · exact hf
        rcases card_cases_of_isList194 hX with hSL | ⟨m, hm, hc⟩ | ⟨m, hm, hc⟩ | hfix | h20160
        · exact hSL
        · exfalso
          refine su3Order_two_pow_ne (m := m) heo (r := 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)))
            (by
              have h1 := Timmesfeld.Orders.odd_pow_sub_one (f := m) (a := 2) (by omega) two_pos
              have h2 := Timmesfeld.Orders.odd_pow_sub_one (f := m) (a := 4) (by omega) four_pos
              exact (by decide : Odd 3).mul (h1.mul h2)) (Or.inl rfl) ?_
          rw [hf, hc]
          ring
        · exfalso
          refine su3Order_two_pow_ne (m := m) heo (r := 3 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)))
            (by
              have h1 := Timmesfeld.Orders.odd_pow_sub_one (f := m) (a := 6) (by omega)
                (by norm_num)
              have h2 := Timmesfeld.Orders.odd_pow_sub_one (f := m) (a := 2) (by omega) two_pos
              exact (by decide : Odd 3).mul (h1.mul h2)) (Or.inr rfl) ?_
          rw [hf, hc]
          ring
        · exact absurd hf (su3Order_ne_of_isFixedOrder hQ1 (Or.inl hfix))
        · exact absurd hf (su3Order_ne_of_isFixedOrder hQ1 (Or.inr h20160))
    ·
      have hp3 : p ≠ 3 := by
        rintro rfl
        have : 3 ∣ 3 ^ e := dvd_pow_self 3 (by omega)
        rcases hiso with ⟨hq, -⟩ | ⟨hq, -⟩ <;> omega
      have hp5 : 5 ≤ p := by
        by_contra hlt
        push Not at hlt
        have := hpp.two_le
        interval_cases p <;> first | omega | exact absurd hpp (by norm_num)
      have hQodd : Odd (p ^ e) := (hpp.odd_of_ne_two hp2).pow
      have hQ5 : 5 ≤ p ^ e := le_trans hp5 (Nat.le_self_pow (by omega) p)
      have hQ3 : ¬ 3 ∣ p ^ e := by rcases hiso with ⟨hq, -⟩ | ⟨hq, -⟩ <;> omega
      have hf : (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1) = 3 * Nat.card X ∨
          (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1) = 3 * Nat.card X := by
        rcases three_mul_card_of_isoLThreePi he hiso with ⟨-, hf, -⟩ | ⟨-, hf⟩
        · exact Or.inl hf
        · exact Or.inr hf
      rcases card_cases_of_isList194 hX with hSL | ⟨m, hm, hc⟩ | ⟨m, hm, hc⟩ | hfix | h20160
      · exact hSL
      · rw [hc] at hf
        exact (false_of_sl3Order_eq_sp4 hQodd hQ5 hQ3 hm hf).elim
      · rw [hc] at hf
        exact (false_of_sl3Order_eq_g2 hQodd hQ5 hQ3 hm hf).elim
      · rcases hf with hf | hf
        · exact absurd hf (sl3Order_ne_of_isFixedOrder hQ1 hfix)
        · exact absurd hf (su3Order_ne_of_isFixedOrder hQ1 (Or.inl hfix))
      · rw [h20160] at hf
        rcases hf with hf | hf
        · have h4 := eq_four_of_sl3Order_eq hQ1 hf
          rw [h4] at hQodd
          exact absurd hQodd (by decide)
        · exact absurd hf (su3Order_ne_of_isFixedOrder hQ1 (Or.inr rfl))
  ·
    have hcard : Nat.card X = 95040 := by
      rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeM12]
    rcases card_cases_of_isList194 hX with hSL | ⟨m, hm, hc⟩ | ⟨m, hm, hc⟩ | hfix | h20160
    · exact hSL
    · exact absurd (hc.symm.trans hcard) (sp4Order_ne_m12 hm)
    · exact absurd (hc.symm.trans hcard) (g2Order_ne_m12 hm)
    · exact absurd (hcard ▸ hfix) not_isFixedOrder_m12.1
    · exact absurd (hcard.symm.trans h20160) not_isFixedOrder_m12.2

end Step1917Steps

end CFSG.RankThree.PartTwo.Sec19
