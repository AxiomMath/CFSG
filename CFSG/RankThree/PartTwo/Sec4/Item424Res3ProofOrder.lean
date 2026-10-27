module

public import CFSG.RankThree.PartTwo.Sec11.Item119
import CFSG.Assembly.OrderReductions.LinearOrders
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item424Res3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem card_sl_three_factor {q : ℕ} (hq : 1 ≤ q) :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) = ((q - 1) ^ 2 * (q + 1)) * (q ^ 3 * (q ^ 2 + q + 1)) := by
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  zify [hq, h2, h3]
  ring

theorem two_pow_le_of_dvd_card_sl_three {q a : ℕ} (hq : Odd q) (hq3 : 3 ≤ q)
    (h : 2 ^ a ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) : 2 ^ a ≤ 2 * q ^ 2 := by
  have hodd : Odd (q ^ 3 * (q ^ 2 + q + 1)) := by
    refine hq.pow.mul ?_
    have : q ^ 2 + q + 1 = q * (q + 1) + 1 := by ring
    rw [this]
    exact (Nat.even_mul_succ_self q).add_one
  have hcop : Nat.Coprime (2 ^ a) (q ^ 3 * (q ^ 2 + q + 1)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
  rw [card_sl_three_factor (by omega)] at h
  have h' : 2 ^ a ∣ (q - 1) ^ 2 * (q + 1) := hcop.dvd_of_dvd_mul_right h
  obtain ⟨k, hk⟩ := hq
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have e : (q - 1) ^ 2 * (q + 1) = (2 * (q - 1) ^ 2) * (2 * j + 1) := by
      have : q + 1 = 2 * (2 * j + 1) := by omega
      rw [this]
      ring
    rw [e] at h'
    have hc : Nat.Coprime (2 ^ a) (2 * j + 1) :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr (odd_two_mul_add_one j))
    have hq1 : 0 < q - 1 := by omega
    have hle := Nat.le_of_dvd (by positivity) (hc.dvd_of_dvd_mul_right h')
    have : (q - 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  · have e : (q - 1) ^ 2 * (q + 1) = (4 * (q + 1)) * (2 * j + 1) ^ 2 := by
      have : q - 1 = 2 * (2 * j + 1) := by omega
      rw [this]
      ring
    rw [e] at h'
    have hc : Nat.Coprime (2 ^ a) ((2 * j + 1) ^ 2) :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr (odd_two_mul_add_one j).pow)
    have hle := Nat.le_of_dvd (by positivity) (hc.dvd_of_dvd_mul_right h')
    have : 4 * (q + 1) ≤ 2 * q ^ 2 := by nlinarith
    omega

theorem eight_mul_lt_card_sl_three {q : ℕ} (hq : 5 ≤ q) :
    8 * q ^ 6 < q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h3]
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℤ) < q := by linarith
  have hq3 : (0 : ℤ) < q ^ 3 := pow_pos hq0 3
  have hq2 : (25 : ℤ) ≤ q ^ 2 := by nlinarith
  have hq32 : (q : ℤ) ^ 2 ≤ q ^ 3 := by
    have : (q : ℤ) ^ 3 = q ^ 2 * q := by ring
    rw [this]
    nlinarith
  have h5 : (25 : ℤ) * q ^ 3 ≤ q ^ 5 := by
    have : (q : ℤ) ^ 5 = q ^ 2 * q ^ 3 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hq2 hq3.le
  have key : (8 : ℤ) * q ^ 3 < (q ^ 2 - 1) * (q ^ 3 - 1) := by
    have : ((q : ℤ) ^ 2 - 1) * (q ^ 3 - 1) = q ^ 5 - q ^ 3 - q ^ 2 + 1 := by ring
    rw [this]
    nlinarith
  have e : (8 : ℤ) * (q : ℤ) ^ 6 = (q : ℤ) ^ 3 * (8 * (q : ℤ) ^ 3) := by ring
  rw [e]
  exact mul_lt_mul_of_pos_left key hq3

theorem false_of_two_pow_dvd {q a N : ℕ} (hq : Odd q) (hq5 : 5 ≤ q)
    (hN : N = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) (hdvd : 2 ^ a ∣ N) (hlt : N < (2 ^ a) ^ 3) :
    False := by
  subst hN
  have h1 := two_pow_le_of_dvd_card_sl_three hq (by omega) hdvd
  have h2 := eight_mul_lt_card_sl_three hq5
  have h3 : (2 ^ a) ^ 3 ≤ (2 * q ^ 2) ^ 3 := Nat.pow_le_pow_left h1 3
  have h4 : (2 * q ^ 2) ^ 3 = 8 * q ^ 6 := by ring
  omega

theorem pow_le_add_one_of_dvd {p f s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hs : 2 ≤ s)
    (h : (p ^ f) ^ 3 ∣ s * (s ^ 2 - 1)) : (p ^ f) ^ 3 ≤ s + 1 := by
  have hpow : (p ^ f) ^ 3 = p ^ (3 * f) := by rw [← pow_mul, mul_comm]
  rw [hpow] at h ⊢
  have hfac : s ^ 2 - 1 = (s - 1) * (s + 1) := by
    have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [this, (by omega : 1 ≤ s)]
    ring
  have hcop : ∀ m : ℕ, ¬ p ∣ m → Nat.Coprime (p ^ (3 * f)) m := fun m hm =>
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  by_cases hps : p ∣ s
  · have hn : ¬ p ∣ s ^ 2 - 1 := by
      intro h1
      have h2 : p ∣ s ^ 2 := dvd_pow hps (by norm_num)
      have h3 : p ∣ s ^ 2 - (s ^ 2 - 1) := Nat.dvd_sub h2 h1
      rw [show s ^ 2 - (s ^ 2 - 1) = 1 by
        have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega] at h3
      exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
    have := Nat.le_of_dvd (by omega) ((hcop _ hn).dvd_of_dvd_mul_right h)
    omega
  · have h1 : p ^ (3 * f) ∣ (s - 1) * (s + 1) := by
      rw [← hfac]
      exact (hcop _ hps).dvd_of_dvd_mul_left h
    by_cases hps1 : p ∣ s - 1
    · have hn : ¬ p ∣ s + 1 := by
        intro h2
        have h3 : p ∣ (s + 1) - (s - 1) := Nat.dvd_sub h2 hps1
        rw [show (s + 1) - (s - 1) = 2 by omega] at h3
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
      have := Nat.le_of_dvd (by omega) ((hcop _ hn).dvd_of_dvd_mul_right h1)
      omega
    · exact Nat.le_of_dvd (by omega) ((hcop _ hps1).dvd_of_dvd_mul_left h1)

theorem false_of_pow_le_add_one {q s : ℕ} (hq5 : 5 ≤ q) (hs : q ^ 3 ≤ s + 1)
    (h : s * (s ^ 2 - 1) = 2 * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))) : False := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq3 : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq5 3
  have hs1 : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [hq2, hs1, (by omega : 1 ≤ q ^ 3)] at h
  have hsQ : ((q : ℤ) ^ 3 - 1) ≤ s := by
    have : ((q ^ 3 : ℕ) : ℤ) ≤ (s : ℤ) + 1 := by exact_mod_cast hs
    push_cast at this
    linarith
  set Q : ℤ := (q : ℤ) ^ 3 with hQ
  have hq5' : (5 : ℤ) ≤ q := by exact_mod_cast hq5
  have hQ125 : (125 : ℤ) ≤ Q := by
    have : ((125 : ℕ) : ℤ) ≤ ((q ^ 3 : ℕ) : ℤ) := by exact_mod_cast hq3
    push_cast at this
    linarith
  have hmono : (Q - 1) * ((Q - 1) ^ 2 - 1) ≤ (s : ℤ) * ((s : ℤ) ^ 2 - 1) := by
    have e : (s : ℤ) * ((s : ℤ) ^ 2 - 1) - (Q - 1) * ((Q - 1) ^ 2 - 1) =
        ((s : ℤ) - (Q - 1)) * ((s : ℤ) ^ 2 + (s : ℤ) * (Q - 1) + (Q - 1) ^ 2 - 1) := by ring
    have h0 : 0 ≤ (s : ℤ) ^ 2 + (s : ℤ) * (Q - 1) + (Q - 1) ^ 2 - 1 := by nlinarith
    have : 0 ≤ ((s : ℤ) - (Q - 1)) * ((s : ℤ) ^ 2 + (s : ℤ) * (Q - 1) + (Q - 1) ^ 2 - 1) :=
      mul_nonneg (by linarith) h0
    linarith
  have hq2' : 2 * ((q : ℤ) ^ 2 - 1) < Q - 2 := by
    rw [hQ]
    nlinarith
  have hpos : 0 < Q * (Q - 1) := by nlinarith
  have hlt : 2 * (Q * (((q : ℤ) ^ 2 - 1) * (Q - 1))) < (Q - 1) * ((Q - 1) ^ 2 - 1) := by
    have e1 : (Q - 1) * ((Q - 1) ^ 2 - 1) = Q * (Q - 1) * (Q - 2) := by ring
    have e2 : 2 * (Q * (((q : ℤ) ^ 2 - 1) * (Q - 1))) = Q * (Q - 1) * (2 * ((q : ℤ) ^ 2 - 1)) := by
      ring
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left hq2' hpos
  linarith

theorem card_projSL_two_two_pow {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (projSL 2 (GaloisField 2 n)) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [Nat.card_congr (Sec4.projSLEquivPSL _).toEquiv,
    CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear _ 2 (by norm_num),
    GaloisField.card 2 n (by omega)]
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    obtain ⟨k, hk⟩ : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    exact Nat.coprime_two_left.mpr ⟨k - 1, by omega⟩
  rw [hg, Nat.div_one]
  simp

theorem two_mul_card_projSL_two_odd {r n : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hn : 1 ≤ n) :
    2 * Nat.card (projSL 2 (GaloisField r n)) = r ^ n * ((r ^ n) ^ 2 - 1) := by
  rw [Nat.card_congr (Sec4.projSLEquivPSL _).toEquiv,
    CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear _ 2 (by norm_num),
    GaloisField.card r n (by omega)]
  have hodd : Odd (r ^ n) := ((Fact.out : r.Prime).odd_of_ne_two hr2).pow
  have hg : Nat.gcd 2 (r ^ n - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    exact Nat.gcd_eq_left ⟨k, by omega⟩
  rw [hg]
  have hev : 2 ∣ r ^ n * ((r ^ n) ^ 2 - 1) := by
    obtain ⟨k, hk⟩ := hodd
    refine Dvd.dvd.mul_left ⟨2 * k * k + 2 * k, ?_⟩ _
    rw [hk]
    zify [show 1 ≤ (2 * k + 1) ^ 2 from Nat.one_le_pow _ _ (by omega)]
    ring
  have e : (r ^ n) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((r ^ n) ^ i - 1) =
      r ^ n * ((r ^ n) ^ 2 - 1) := by
    simp
  rw [e]
  exact Nat.mul_div_cancel' hev

theorem card_projSL_three_two_pow {n : ℕ} (hn : 1 ≤ n) (h : 2 ^ n % 3 = 2) :
    Nat.card (projSL 3 (GaloisField 2 n)) =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  obtain ⟨φ⟩ := KFacts.nonempty_projSL_mulEquiv 3 (GaloisField 2 n)
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  rw [Nat.card_congr φ.toEquiv, LocalAnalysis.ComponentInitial.LinearFlag.card_projectiveSL,
    KFacts.scalars_three_eq_bot_of_mod_three (by rw [hK]; exact h), Subgroup.card_bot,
    Nat.div_one, KFacts.card_sl_three_eq, hK]

theorem card_projSU_three_two_pow {n : ℕ} (hn : 1 ≤ n) (h : 2 ^ n % 3 = 1) :
    Nat.card (projSU 3 2 n) = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
  have hU : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
    ⟨Nat.prime_two, hn, GaloisField.card 2 _ (by omega)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := KFacts.nonempty_unitaryPSU_mulEquiv_projSU hU
  have hZ := ClassicalGroups.UnitaryFlag.card_unitaryScalars hU (n := 3) (by norm_num)
  have hg : Nat.gcd 3 (2 ^ n + 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
  have hSU := GH74.GLS.Stage2.Signalizer.Odd87.card_unitarySU_three hU
  rw [(ClassicalGroups.UnitaryFlag.unitaryScalars hU 3).card_eq_card_quotient_mul_card_subgroup,
    hZ, hg, mul_one] at hSU
  rw [← Nat.card_congr φ.toEquiv]
  exact hSU

theorem not_isType424_of_card {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f)
    (hX : Nat.card X = (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1))) :
    ¬ Sec11.IsType424 X := by
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  rintro (⟨n, hn, ⟨e⟩⟩ | ⟨r, n, hr, hr3, hn, ⟨e⟩⟩ | ⟨n, hn, h⟩)
  ·
    have hc := card_projSL_two_two_pow hn
    rw [← Nat.card_congr e.toEquiv] at hc
    refine false_of_two_pow_dvd hq hq5 hX (a := n) ⟨_, hc⟩ ?_
    rw [hc]
    have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have : (2 ^ n) ^ 2 - 1 < (2 ^ n) ^ 2 := by omega
    calc 2 ^ n * ((2 ^ n) ^ 2 - 1) < 2 ^ n * (2 ^ n) ^ 2 :=
          Nat.mul_lt_mul_of_pos_left this (by positivity)
      _ = (2 ^ n) ^ 3 := by ring
  ·
    have hc := two_mul_card_projSL_two_odd (r := r) (by omega) hn
    rw [← Nat.card_congr e.toEquiv, hX] at hc
    have hs : 2 ≤ r ^ n :=
      (Fact.out : r.Prime).two_le.trans (Nat.le_self_pow (by omega) r)
    have hdvd : (p ^ f) ^ 3 ∣ r ^ n * ((r ^ n) ^ 2 - 1) := by
      rw [← hc]
      exact Dvd.dvd.mul_left (Dvd.intro _ rfl) 2
    exact false_of_pow_le_add_one hq5 (pow_le_add_one_of_dvd hp hp2 hs hdvd) hc.symm
  · rcases h with ⟨h1, ⟨e⟩⟩ | ⟨h2, ⟨e⟩⟩
    ·
      have hc := card_projSU_three_two_pow hn h1
      rw [← Nat.card_congr e.toEquiv] at hc
      refine false_of_two_pow_dvd hq hq5 hX (a := 3 * n)
        ⟨((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1), by rw [hc, pow_mul']; ring⟩ ?_
      · rw [hc, pow_mul']
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
      refine false_of_two_pow_dvd hq hq5 hX (a := 3 * n)
        ⟨((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1), by rw [hc, pow_mul']⟩ ?_
      · rw [hc, pow_mul']
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
