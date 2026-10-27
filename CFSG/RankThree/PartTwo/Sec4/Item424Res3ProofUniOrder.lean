module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofOrder

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item424Res3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem card_su_three_factor {q : ℕ} (hq : 1 ≤ q) :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) =
      ((q - 1) * (q + 1) ^ 2) * (q ^ 3 * (q ^ 2 - q + 1)) := by
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqq : q ≤ q ^ 2 := by nlinarith
  zify [hq, h2, hqq]
  ring

theorem two_pow_le_of_dvd_card_su_three {q a : ℕ} (hq : Odd q) (hq3 : 3 ≤ q)
    (h : 2 ^ a ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) : 2 ^ a ≤ 2 * (q + 1) ^ 2 := by
  have hodd : Odd (q ^ 3 * (q ^ 2 - q + 1)) := by
    refine hq.pow.mul ?_
    have : q ^ 2 - q + 1 = q * (q - 1) + 1 := by
      have hqq : q ≤ q ^ 2 := by nlinarith
      zify [hqq, (by omega : 1 ≤ q)]
      ring
    rw [this]
    obtain ⟨k, hk⟩ := hq
    exact (Nat.even_mul.mpr (Or.inr ⟨k, by omega⟩)).add_one
  have hcop : Nat.Coprime (2 ^ a) (q ^ 3 * (q ^ 2 - q + 1)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
  rw [card_su_three_factor (by omega)] at h
  have h' : 2 ^ a ∣ (q - 1) * (q + 1) ^ 2 := hcop.dvd_of_dvd_mul_right h
  obtain ⟨k, hk⟩ := hq
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have e : (q - 1) * (q + 1) ^ 2 = (4 * (q - 1)) * (2 * j + 1) ^ 2 := by
      have : q + 1 = 2 * (2 * j + 1) := by omega
      rw [this]
      ring
    rw [e] at h'
    have hc : Nat.Coprime (2 ^ a) ((2 * j + 1) ^ 2) :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr (odd_two_mul_add_one j).pow)
    have hq1 : 0 < q - 1 := by omega
    have hle := Nat.le_of_dvd (by positivity) (hc.dvd_of_dvd_mul_right h')
    have : 4 * (q - 1) ≤ 2 * (q + 1) ^ 2 :=
      calc 4 * (q - 1) ≤ 4 * q := by omega
        _ ≤ 2 * (q + 1) ^ 2 := by nlinarith
    omega
  · have e : (q - 1) * (q + 1) ^ 2 = (2 * (q + 1) ^ 2) * (2 * j + 1) := by
      have : q - 1 = 2 * (2 * j + 1) := by omega
      rw [this]
      ring
    rw [e] at h'
    have hc : Nat.Coprime (2 ^ a) (2 * j + 1) :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr (odd_two_mul_add_one j))
    exact Nat.le_of_dvd (by positivity) (hc.dvd_of_dvd_mul_right h')

theorem eight_mul_lt_card_su_three {q : ℕ} (hq : 7 ≤ q) :
    8 * (q + 1) ^ 6 < q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h2]
  have hq' : (7 : ℤ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℤ) < q := by linarith
  have hq3 : (0 : ℤ) < q ^ 3 := pow_pos hq0 3
  have h1 : (7 : ℤ) * (q + 1) ≤ 8 * q := by linarith
  have h6 : ((7 : ℤ) * (q + 1)) ^ 6 ≤ (8 * q) ^ 6 :=
    pow_le_pow_left₀ (by positivity) h1 6
  have h6' : (117649 : ℤ) * (q + 1) ^ 6 ≤ 262144 * q ^ 6 := by
    have e1 : ((7 : ℤ) * (q + 1)) ^ 6 = 117649 * (q + 1) ^ 6 := by ring
    have e2 : ((8 : ℤ) * q) ^ 6 = 262144 * q ^ 6 := by ring
    rw [e1, e2] at h6
    exact h6
  have hq2 : (49 : ℤ) ≤ q ^ 2 := by nlinarith
  have hb : (48 : ℤ) * q ^ 3 ≤ (q ^ 2 - 1) * (q ^ 3 + 1) := by
    have e : ((q : ℤ) ^ 2 - 1) * (q ^ 3 + 1) = (q ^ 2 - 1) * q ^ 3 + (q ^ 2 - 1) := by ring
    rw [e]
    have : (48 : ℤ) * q ^ 3 ≤ (q ^ 2 - 1) * q ^ 3 := by
      have := mul_le_mul_of_nonneg_right (by linarith : (48 : ℤ) ≤ q ^ 2 - 1) hq3.le
      linarith
    nlinarith
  have hc : (48 : ℤ) * q ^ 6 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    have := mul_le_mul_of_nonneg_left hb hq3.le
    have e : (q : ℤ) ^ 3 * (48 * q ^ 3) = 48 * q ^ 6 := by ring
    linarith
  have hq6 : (0 : ℤ) < q ^ 6 := pow_pos hq0 6
  nlinarith

theorem false_of_two_pow_dvd_su {q a N : ℕ} (hq : Odd q) (hq7 : 7 ≤ q)
    (hN : N = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) (hdvd : 2 ^ a ∣ N) (hlt : N < (2 ^ a) ^ 3) :
    False := by
  subst hN
  have h1 := two_pow_le_of_dvd_card_su_three hq (by omega) hdvd
  have h2 := eight_mul_lt_card_su_three hq7
  have h3 : (2 ^ a) ^ 3 ≤ (2 * (q + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left h1 3
  have h4 : (2 * (q + 1) ^ 2) ^ 3 = 8 * (q + 1) ^ 6 := by ring
  omega

theorem false_of_pow_le_add_one_su {q s : ℕ} (hq7 : 7 ≤ q) (hs : q ^ 3 ≤ s + 1)
    (h : s * (s ^ 2 - 1) = 2 * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)))) : False := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq3 : 343 ≤ q ^ 3 := by
    calc 343 = 7 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq7 3
  have hs1 : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [hq2, hs1] at h
  have hsQ : ((q : ℤ) ^ 3 - 1) ≤ s := by
    have : ((q ^ 3 : ℕ) : ℤ) ≤ (s : ℤ) + 1 := by exact_mod_cast hs
    push_cast at this
    linarith
  set Q : ℤ := (q : ℤ) ^ 3 with hQ
  have hq7' : (7 : ℤ) ≤ q := by exact_mod_cast hq7
  have hQ343 : (343 : ℤ) ≤ Q := by
    have : ((343 : ℕ) : ℤ) ≤ ((q ^ 3 : ℕ) : ℤ) := by exact_mod_cast hq3
    push_cast at this
    linarith
  have hmono : (Q - 1) * ((Q - 1) ^ 2 - 1) ≤ (s : ℤ) * ((s : ℤ) ^ 2 - 1) := by
    have e : (s : ℤ) * ((s : ℤ) ^ 2 - 1) - (Q - 1) * ((Q - 1) ^ 2 - 1) =
        ((s : ℤ) - (Q - 1)) * ((s : ℤ) ^ 2 + (s : ℤ) * (Q - 1) + (Q - 1) ^ 2 - 1) := by ring
    have h0 : 0 ≤ (s : ℤ) ^ 2 + (s : ℤ) * (Q - 1) + (Q - 1) ^ 2 - 1 := by nlinarith
    have : 0 ≤ ((s : ℤ) - (Q - 1)) * ((s : ℤ) ^ 2 + (s : ℤ) * (Q - 1) + (Q - 1) ^ 2 - 1) :=
      mul_nonneg (by linarith) h0
    linarith
  have hq2' : (49 : ℤ) ≤ (q : ℤ) ^ 2 := by nlinarith
  have hQq : 7 * (q : ℤ) ^ 2 ≤ Q := by
    rw [hQ]
    have e : (q : ℤ) ^ 3 = q * q ^ 2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hq7' (by positivity)
  have key : 2 * (((q : ℤ) ^ 2 - 1) * (Q + 1)) < (Q - 1) * (Q - 2) := by
    nlinarith
  have hlt : 2 * (Q * (((q : ℤ) ^ 2 - 1) * (Q + 1))) < (Q - 1) * ((Q - 1) ^ 2 - 1) := by
    have e1 : (Q - 1) * ((Q - 1) ^ 2 - 1) = Q * ((Q - 1) * (Q - 2)) := by ring
    have e2 : 2 * (Q * (((q : ℤ) ^ 2 - 1) * (Q + 1))) =
        Q * (2 * (((q : ℤ) ^ 2 - 1) * (Q + 1))) := by
      ring
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left key (by linarith)
  linarith

theorem not_isType424_of_card_su {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq7 : 7 ≤ p ^ f)
    (hX : Nat.card X = (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) :
    ¬ Sec11.IsType424 X := by
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hX' : Nat.card X = (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
    rw [hX, mul_assoc]
  rintro (⟨n, hn, ⟨e⟩⟩ | ⟨r, n, hr, hr3, hn, ⟨e⟩⟩ | ⟨n, hn, h⟩)
  ·
    have hc := card_projSL_two_two_pow hn
    rw [← Nat.card_congr e.toEquiv] at hc
    refine false_of_two_pow_dvd_su hq hq7 hX' (a := n) ⟨_, hc⟩ ?_
    rw [hc]
    have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have : (2 ^ n) ^ 2 - 1 < (2 ^ n) ^ 2 := by omega
    calc 2 ^ n * ((2 ^ n) ^ 2 - 1) < 2 ^ n * (2 ^ n) ^ 2 :=
          Nat.mul_lt_mul_of_pos_left this (by positivity)
      _ = (2 ^ n) ^ 3 := by ring
  ·
    have hc := two_mul_card_projSL_two_odd (r := r) (by omega) hn
    rw [← Nat.card_congr e.toEquiv, hX'] at hc
    have hs : 2 ≤ r ^ n :=
      (Fact.out : r.Prime).two_le.trans (Nat.le_self_pow (by omega) r)
    have hdvd : (p ^ f) ^ 3 ∣ r ^ n * ((r ^ n) ^ 2 - 1) := by
      rw [← hc]
      exact Dvd.dvd.mul_left (Dvd.intro _ rfl) 2
    exact false_of_pow_le_add_one_su hq7 (pow_le_add_one_of_dvd hp hp2 hs hdvd) hc.symm
  · rcases h with ⟨h1, ⟨e⟩⟩ | ⟨h2, ⟨e⟩⟩
    ·
      have hc := card_projSU_three_two_pow hn h1
      rw [← Nat.card_congr e.toEquiv] at hc
      refine false_of_two_pow_dvd_su hq hq7 hX' (a := 3 * n)
        ⟨((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1), by rw [hc, pow_mul']; ring⟩ ?_
      rw [hc, pow_mul']
      set t := 2 ^ n with ht
      have ht2 : 2 ≤ t := by
        rw [ht]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have h1' : 1 ≤ t ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1']
      have ht' : (2 : ℤ) ≤ t := by exact_mod_cast ht2
      nlinarith [pow_pos (by linarith : (0 : ℤ) < t) 3, pow_pos (by linarith : (0 : ℤ) < t) 5,
        pow_pos (by linarith : (0 : ℤ) < t) 6, pow_pos (by linarith : (0 : ℤ) < t) 8]
    ·
      have hc := card_projSL_three_two_pow hn h2
      rw [← Nat.card_congr e.toEquiv] at hc
      refine false_of_two_pow_dvd_su hq hq7 hX' (a := 3 * n)
        ⟨((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1), by rw [hc, pow_mul']⟩ ?_
      rw [hc, pow_mul']
      set t := 2 ^ n with ht
      have ht2 : 2 ≤ t := by
        rw [ht]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have h1' : 1 ≤ t ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h1'' : 1 ≤ t ^ 3 := Nat.one_le_pow _ _ (by omega)
      zify [h1', h1'']
      have ht' : (2 : ℤ) ≤ t := by exact_mod_cast ht2
      nlinarith [pow_pos (by linarith : (0 : ℤ) < t) 3, pow_pos (by linarith : (0 : ℤ) < t) 5,
        pow_pos (by linarith : (0 : ℤ) < t) 6, pow_pos (by linarith : (0 : ℤ) < t) 8]

end CFSG.RankThree.PartTwo.Sec4.Item424Res3
