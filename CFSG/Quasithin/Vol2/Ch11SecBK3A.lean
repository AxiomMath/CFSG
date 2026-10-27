module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL34B
public import CFSG.Quasithin.Vol2.Ch11SecE41Two
public import CFSG.Quasithin.Vol2.Ch11SecAKDa
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU)

namespace BK3

theorem eq_of_two_pow_mul_odd {a b r s : ℕ} (hr : Odd r) (hs : Odd s)
    (h : 2 ^ a * r = 2 ^ b * s) : a = b ∧ r = s := by
  have h2 := congrArg (padicValNat 2) h
  have hr2 : ¬ 2 ∣ r := by have := Nat.odd_iff.mp hr; omega
  have hs2 : ¬ 2 ∣ s := by have := Nat.odd_iff.mp hs; omega
  rw [padicValNat.mul (by positivity) hr.pos.ne', padicValNat.mul (by positivity) hs.pos.ne',
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hr2,
    padicValNat.eq_zero_of_not_dvd hs2, add_zero, add_zero] at h2
  subst h2
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

theorem odd_pow_sub_one {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) : Odd ((2 ^ n) ^ j - 1) := by
  rw [← pow_mul]
  exact Nat.Even.sub_odd Nat.one_le_two_pow
    (Nat.even_pow.mpr ⟨even_two, by positivity⟩) odd_one

theorem two_pow_six_dvd {a m c : ℕ} (ha : 6 ≤ a) (h : 2 ^ a * m = c) : 2 ^ 6 ∣ c :=
  (pow_dvd_pow 2 ha).trans (h ▸ Dvd.intro m rfl)

variable {X : Type} [Group X]

theorem card_of_rankTwoShape {n : ℕ} (hn : 2 ≤ n) (h : RankTwoShape X n) :
    ∃ a m : ℕ, Nat.card X = 2 ^ a * m ∧ Odd m ∧ 6 ≤ a ∧ m + 1 < 4 ^ a ∧
      (a = 6 → Nat.card X = 60480 ∨ IsPSL 3 2 2 X) := by
  have hq : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
  have hpow4 : ∀ c : ℕ, (4 : ℕ) ^ (c * n) = (2 ^ n) ^ (2 * c) := fun c => by
    rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring_nf
  rcases h with ⟨K, _, _, hK, ⟨e⟩⟩ | hL | hS | hG
  ·
    refine ⟨3 * n, ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1), ?_,
      (odd_pow_sub_one (by omega) (by omega)).mul (odd_pow_sub_one (by omega) (by omega)),
      by omega, ?_, fun h6 => Or.inl ?_⟩
    · rw [Nat.card_congr e.toEquiv, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
        (by norm_num), hK, show Finset.Icc 2 3 = {2, 3} by decide,
        Finset.prod_pair (by norm_num), show 3 * (3 - 1) / 2 = 3 by norm_num, ← pow_mul,
        mul_comm n 3]
    · rw [hpow4 3]
      calc ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) + 1 ≤ (2 ^ n) ^ 2 * (2 ^ n) ^ 3 := by
            have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
            have h2 : 1 ≤ (2 ^ n) ^ 3 := Nat.one_le_pow _ _ (by positivity)
            have := Nat.mul_lt_mul'' (Nat.sub_lt h1 one_pos) (Nat.sub_lt h2 one_pos)
            omega
        _ < (2 ^ n) ^ (2 * 3) := by
            rw [← pow_add]
            exact Nat.pow_lt_pow_right hq (by norm_num)
    · have hn2 : n = 2 := by omega
      subst hn2
      rw [Nat.card_congr e.toEquiv, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
        (by norm_num), hK, show Finset.Icc 2 3 = {2, 3} by decide,
        Finset.prod_pair (by norm_num)]
      norm_num
  ·
    obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
    have hcard : Nat.card X = (2 ^ n) ^ (3 * (3 - 1) / 2) *
        (∏ j ∈ Finset.Icc 2 3, ((2 ^ n) ^ j - 1)) / Nat.gcd 3 (2 ^ n - 1) := by
      rw [Nat.card_congr φ.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
    set A := ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) with hA
    set d := Nat.gcd 3 (2 ^ n - 1) with hd
    have hprod : (∏ j ∈ Finset.Icc 2 3, ((2 ^ n) ^ j - 1)) = A := by
      rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
    have hdA : d ∣ A := by
      refine (Nat.gcd_dvd_right 3 _).trans (Dvd.dvd.mul_left ?_ _)
      simpa using Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 3
    have hAodd : Odd A :=
      (odd_pow_sub_one (by omega) (by omega)).mul (odd_pow_sub_one (by omega) (by omega))
    have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ (by norm_num)
    refine ⟨3 * n, A / d, ?_, ?_, by omega, ?_, fun h6 => Or.inr ?_⟩
    · rw [hcard, hprod, show 3 * (3 - 1) / 2 = 3 by norm_num, Nat.mul_div_assoc _ hdA,
        ← pow_mul, mul_comm n 3]
    · obtain ⟨k, hk⟩ := hdA
      have hk' : A / d = k := by rw [hk, Nat.mul_div_cancel_left _ hd0]
      rw [hk']
      rw [hk] at hAodd
      exact (Nat.odd_mul.mp hAodd).2
    · have hle : A / d ≤ A := Nat.div_le_self _ _
      rw [hpow4 3]
      calc A / d + 1 ≤ A + 1 := by omega
        _ ≤ (2 ^ n) ^ 2 * (2 ^ n) ^ 3 := by
            have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
            have h2 : 1 ≤ (2 ^ n) ^ 3 := Nat.one_le_pow _ _ (by positivity)
            have := Nat.mul_lt_mul'' (Nat.sub_lt h1 one_pos) (Nat.sub_lt h2 one_pos)
            rw [hA]
            omega
        _ < (2 ^ n) ^ (2 * 3) := by
            rw [← pow_add]
            exact Nat.pow_lt_pow_right hq (by norm_num)
    · have hn2 : n = 2 := by omega
      subst hn2
      exact CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
  ·
    obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hS
    have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    have hcard : Nat.card X = (2 ^ n) ^ (2 ^ 2) *
        ∏ j ∈ Finset.Icc 1 2, ((2 ^ n) ^ (2 * j) - 1) := by
      rw [Nat.card_congr φ.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hK]
    refine ⟨4 * n, ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1), ?_,
      (odd_pow_sub_one (by omega) (by omega)).mul (odd_pow_sub_one (by omega) (by omega)),
      by omega, ?_, fun h6 => by omega⟩
    · rw [hcard, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num),
        ← pow_mul, mul_comm n (2 ^ 2)]
      norm_num
    · rw [hpow4 4]
      calc ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1) + 1 ≤ (2 ^ n) ^ 2 * (2 ^ n) ^ 4 := by
            have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
            have h2 : 1 ≤ (2 ^ n) ^ 4 := Nat.one_le_pow _ _ (by positivity)
            have := Nat.mul_lt_mul'' (Nat.sub_lt h1 one_pos) (Nat.sub_lt h2 one_pos)
            omega
        _ < (2 ^ n) ^ (2 * 4) := by
            rw [← pow_add]
            exact Nat.pow_lt_pow_right hq (by norm_num)
  ·
    have hcard := Ch11.SecE.card_of_lieModel_G2 SecA.factG2AdjointOrder_holds (by omega) hG
    refine ⟨6 * n, ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1), ?_,
      (odd_pow_sub_one (by omega) (by omega)).mul (odd_pow_sub_one (by omega) (by omega)),
      by omega, ?_, fun h6 => by omega⟩
    · rw [hcard, SecA.oG2, ← pow_mul, ← pow_mul, mul_comm n 6, mul_comm n 2]
    · rw [hpow4 6]
      calc ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) + 1 ≤ (2 ^ n) ^ 6 * (2 ^ n) ^ 2 := by
            have h1 : 1 ≤ (2 ^ n) ^ 6 := Nat.one_le_pow _ _ (by positivity)
            have h2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
            have := Nat.mul_lt_mul'' (Nat.sub_lt h1 one_pos) (Nat.sub_lt h2 one_pos)
            omega
        _ < (2 ^ n) ^ (2 * 6) := by
            rw [← pow_add]
            exact Nat.pow_lt_pow_right hq (by norm_num)

omit [Group X] in
theorem odd_four_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (4 ^ k - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) (Nat.even_pow.mpr ⟨by decide, by omega⟩)
    odd_one

theorem card_PSL2 {k : ℕ} (hk : 1 ≤ k) (h : LieModel X .PSL 2 2 k) :
    Nat.card X = 2 ^ k * (4 ^ k - 1) := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel
    (by decide) h
  rw [Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL
    (by norm_num), hK, Finset.Icc_self, Finset.prod_singleton,
    show Nat.gcd 2 (2 ^ k - 1) = 1 from Nat.coprime_two_left.mpr
      (Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one),
    Nat.div_one, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one, ← pow_mul, mul_comm k 2,
    pow_mul]
  norm_num

theorem card_PSL321 (h : LieModel X .PSL 3 2 1) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two (h.statedClassicalModel (by decide))

theorem card_PSL421 (h : LieModel X .PSL 4 2 1) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two (h.statedClassicalModel (by decide))

theorem card_PSU331 (h : StatedClassicalModel X .PSU 3 3 1) : Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem card_hat6 [Finite X] (hZ : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) : Nat.card X = 1080 := by
  rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr e.toEquiv,
    card_alt6, hZ]

theorem card_ne_of_not_dvd {n c : ℕ} (hn : 2 ≤ n) (h : RankTwoShape X n)
    (hc : ¬ 2 ^ 6 ∣ c) : Nat.card X ≠ c := by
  obtain ⟨a, m, hcard, -, ha, -, -⟩ := card_of_rankTwoShape hn h
  intro hX
  exact hc (two_pow_six_dvd ha (hcard.symm.trans hX))

theorem card_ne_L2 {n k : ℕ} (hn : 2 ≤ n) (h : RankTwoShape X n) (hk : 1 ≤ k) :
    Nat.card X ≠ 2 ^ k * (4 ^ k - 1) := by
  obtain ⟨a, m, hcard, hm, -, hma, -⟩ := card_of_rankTwoShape hn h
  intro hX
  obtain ⟨rfl, rfl⟩ := eq_of_two_pow_mul_odd hm (odd_four_pow_sub_one hk) (hcard.symm.trans hX)
  have : 1 ≤ 4 ^ a := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem isPSL322_of_card {n : ℕ} (hn : 2 ≤ n) (h : RankTwoShape X n)
    (hX : Nat.card X = 20160) : IsPSL 3 2 2 X := by
  obtain ⟨a, m, hcard, hm, -, -, h6⟩ := card_of_rankTwoShape hn h
  obtain ⟨rfl, -⟩ := eq_of_two_pow_mul_odd hm (by decide : Odd 315)
    (hcard.symm.trans (hX.trans (show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num)))
  rcases h6 rfl with h | h
  · omega
  · exact h

end BK3

theorem factNotSmall443_holds : FactNotSmall443 := by
  intro X _ _ n hn hX hS
  rcases hS with ⟨k, hk, hL2⟩ | hL32 | hL42 | hA6 | hA7 | ⟨-, hZ, hZe⟩ | hU33
  · exact BK3.card_ne_L2 hn hX (by omega) (BK3.card_PSL2 (by omega) hL2)
  · exact BK3.card_ne_of_not_dvd hn hX (by norm_num) (BK3.card_PSL321 hL32)
  · exact Ch11.SecS.factL34NotL42_holds X (BK3.isPSL322_of_card hn hX (BK3.card_PSL421 hL42))
      (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL42)
  · obtain ⟨e⟩ := hA6
    exact BK3.card_ne_of_not_dvd hn hX (by norm_num)
      ((Nat.card_congr e.toEquiv).trans BK3.card_alt6)
  · obtain ⟨e⟩ := hA7
    exact BK3.card_ne_of_not_dvd hn hX (by norm_num)
      ((Nat.card_congr e.toEquiv).trans BK3.card_alt7)
  · obtain ⟨e⟩ := hZe
    exact BK3.card_ne_of_not_dvd hn hX (by norm_num) (BK3.card_hat6 hZ e)
  · exact BK3.card_ne_of_not_dvd hn hX (by norm_num)
      (BK3.card_PSU331 (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hU33))

end CFSG.Quasithin.Vol2.Ch11.SecB
