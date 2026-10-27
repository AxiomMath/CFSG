module

import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.Sporadic.Mathieu.M24
import CFSG.Sporadic.He.Simple
import CFSG.Sporadic.Ru
import CFSG.Sporadic.J4
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.Item218ProofU4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Blueprint

namespace Item218Res2Proof

theorem padicValNat_two_pow_cube_mul_odd {a x : ℕ} (hx : Odd x) :
    padicValNat 2 ((2 ^ a) ^ 3 * x) = 3 * a := by
  rw [← pow_mul, padicValNat.mul (by positivity) hx.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hx.not_two_dvd_nat, add_zero, mul_comm]

theorem padicValNat_two_pow_mul_odd' {k x : ℕ} (hx : Odd x) : padicValNat 2 (2 ^ k * x) = k := by
  rw [padicValNat.mul (by positivity) hx.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hx.not_two_dvd_nat, add_zero]

theorem odd_sl3Part {n : ℕ} (hn : 1 ≤ n) : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
  (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
    (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))

theorem card_projSL_mul_three {n : ℕ} (hn : Even n) (hn1 : 1 ≤ n) :
    Nat.card (projSL 3 (GaloisField 2 n)) * 3 =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 n)
  rw [GaloisField.card 2 n (by omega)] at h
  have hg : Nat.gcd 3 (2 ^ n - 1) = 3 := by
    obtain ⟨k, rfl⟩ := hn
    apply Nat.gcd_eq_left
    rw [← two_mul, pow_mul]
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp
      (by rw [Nat.ModEq, Nat.pow_mod]; norm_num)
  rwa [hg] at h

theorem padicValNat_card_projSL {n : ℕ} (hn : Even n) (hn1 : 1 ≤ n) :
    padicValNat 2 (Nat.card (projSL 3 (GaloisField 2 n))) = 3 * n := by
  have h0 := card_projSL_mul_three hn hn1
  have hP : Nat.card (projSL 3 (GaloisField 2 n)) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h0
    have : 0 < (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
      Nat.mul_pos (by positivity) (odd_sl3Part hn1).pos
    omega
  have h := congrArg (padicValNat 2) h0
  rw [padicValNat.mul hP (by norm_num),
    padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by norm_num), add_zero,
    padicValNat_two_pow_cube_mul_odd (odd_sl3Part hn1)] at h
  exact h

theorem card_SL3 {n : ℕ} (hn1 : 1 ≤ n) :
    Nat.card (SL3 n) = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  rw [KFacts.card_SL_three, ← Nat.card_eq_fintype_card, GaloisField.card 2 n (by omega),
    mul_assoc]

theorem three_mul_ordG2_lt {r : ℕ} (hr : 2 ≤ r) :
    3 * CFSG.Open.ordG2 r < (r ^ 2) ^ 3 * (((r ^ 2) ^ 2 - 1) * ((r ^ 2) ^ 3 - 1)) := by
  rw [CFSG.Open.ordG2]
  have h2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ (r ^ 2) ^ 2 := Nat.one_le_pow _ _ h2
  have h6 : 1 ≤ (r ^ 2) ^ 3 := Nat.one_le_pow _ _ h2
  have h6' : 1 ≤ r ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h4, h6, h6']
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have ha : 0 < (r : ℤ) ^ 6 - 1 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2) hr' 6]
  have hb : 0 < (r : ℤ) ^ 2 - 1 := by nlinarith
  have hpos : 0 < (r : ℤ) ^ 6 * (((r : ℤ) ^ 6 - 1) * ((r : ℤ) ^ 2 - 1)) := by positivity
  have hkey : (3 : ℤ) < (r : ℤ) ^ 2 + 1 := by nlinarith
  have e : ((r : ℤ) ^ 2) ^ 3 * ((((r : ℤ) ^ 2) ^ 2 - 1) * (((r : ℤ) ^ 2) ^ 3 - 1)) =
      (r : ℤ) ^ 6 * (((r : ℤ) ^ 6 - 1) * ((r : ℤ) ^ 2 - 1)) * ((r : ℤ) ^ 2 + 1) := by ring
  rw [e]
  nlinarith

theorem three_mul_ordTrialityD4_lt {r : ℕ} (hr : 2 ≤ r) :
    3 * CFSG.Open.ordTrialityD4 r < (r ^ 4) ^ 3 * (((r ^ 4) ^ 2 - 1) * ((r ^ 4) ^ 3 - 1)) := by
  rw [CFSG.Open.ordTrialityD4]
  have h2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ r ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ r ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h8 : 1 ≤ (r ^ 4) ^ 2 := Nat.one_le_pow _ _ h4
  have h12 : 1 ≤ (r ^ 4) ^ 3 := Nat.one_le_pow _ _ h4
  zify [h2, h6, h8, h12]
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have h1 : ((r : ℤ) ^ 4) ^ 3 * ((((r : ℤ) ^ 4) ^ 2 - 1) * (((r : ℤ) ^ 4) ^ 3 - 1)) =
      (r : ℤ) ^ 12 * (((r : ℤ) ^ 6 - 1) * ((r : ℤ) ^ 2 - 1)) *
        (((r : ℤ) ^ 6 + 1) * ((r : ℤ) ^ 2 + 1) * ((r : ℤ) ^ 4 + 1)) := by ring
  have h2' : 3 * ((r : ℤ) ^ 12 * ((r : ℤ) ^ 8 + (r : ℤ) ^ 4 + 1) * ((r : ℤ) ^ 6 - 1) *
      ((r : ℤ) ^ 2 - 1)) = (r : ℤ) ^ 12 * (((r : ℤ) ^ 6 - 1) * ((r : ℤ) ^ 2 - 1)) *
        (3 * ((r : ℤ) ^ 8 + (r : ℤ) ^ 4 + 1)) := by ring
  rw [h1, h2']
  have ha : 0 < (r : ℤ) ^ 6 - 1 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2) hr' 6]
  have hb : 0 < (r : ℤ) ^ 2 - 1 := by nlinarith
  have hpos : 0 < (r : ℤ) ^ 12 * (((r : ℤ) ^ 6 - 1) * ((r : ℤ) ^ 2 - 1)) := by positivity
  have hkey : 3 * ((r : ℤ) ^ 8 + (r : ℤ) ^ 4 + 1) <
      ((r : ℤ) ^ 6 + 1) * ((r : ℤ) ^ 2 + 1) * ((r : ℤ) ^ 4 + 1) := by
    have h4' : 16 ≤ (r : ℤ) ^ 4 := by
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2) hr' 4]
    have h8' : 0 < (r : ℤ) ^ 8 := by positivity
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2) hr' 2]
  exact mul_lt_mul_of_pos_left hkey hpos

section List

theorem not_isList218_of_lThree
    {G : Type} [Group G]
    [Finite G] {X : Subgroup G} (hX : IsList218 X) {n : ℕ} (hn0 : 0 < n) (hn : Even n)
    (h7 : Nonempty (lBar X ≃* projSL 3 (GaloisField 2 n)) ∨ Nonempty (lBar X ≃* SL3 n)) :
    False := by
  have hn1 : 1 ≤ n := hn0
  have hcard : Nat.card (lBar X) * 3 = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ∨
      Nat.card (lBar X) = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
    rcases h7 with e | e
    · left
      rw [Nat.card_congr e.some.toEquiv, card_projSL_mul_three hn hn1]
    · right
      rw [Nat.card_congr e.some.toEquiv, card_SL3 hn1]
  have hv : padicValNat 2 (Nat.card (lBar X)) = 3 * n := by
    rcases h7 with e | e
    · rw [Nat.card_congr e.some.toEquiv, padicValNat_card_projSL hn hn1]
    · rw [Nat.card_congr e.some.toEquiv, card_SL3 hn1, padicValNat_two_pow_cube_mul_odd
        (odd_sl3Part hn1)]
  obtain ⟨k, rfl⟩ := hn
  rcases hX with hf | hf | hf | hf | hf | ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [Nat.card_congr hf.some.toEquiv, Sporadic.Mathieu.card_M24,
      show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num,
      padicValNat_two_pow_mul_odd' (by decide)] at hv
    omega
  · rw [Nat.card_congr hf.some.toEquiv, Sporadic.He.card_He,
      show (4030387200 : ℕ) = 2 ^ 10 * 3935925 by norm_num,
      padicValNat_two_pow_mul_odd' (by decide)] at hv
    omega
  · rw [Nat.card_congr hf.some.toEquiv, KFacts.KS14.card_nativeJ2,
      show (604800 : ℕ) = 2 ^ 7 * 4725 by norm_num, padicValNat_two_pow_mul_odd' (by decide)] at hv
    omega
  · rw [Nat.card_congr hf.some.toEquiv, Sporadic.Ru.card_Ru,
      show (145926144000 : ℕ) = 2 ^ 14 * 8906625 by norm_num,
      padicValNat_two_pow_mul_odd' (by decide)] at hv
    omega
  · rw [Nat.card_congr hf.some.toEquiv, Sporadic.J4.card_J4,
      show (86775571046077562880 : ℕ) = 2 ^ 21 * 41377816699065 by norm_num,
      padicValNat_two_pow_mul_odd' (by decide)] at hv
    omega
  ·
    have hm1 : 1 ≤ m := hm.1.2.1
    have hc : Nat.card (lBar X) = CFSG.Open.ordG2 (2 ^ m) :=
      Timmesfeld.card_chevalleyExceptionalModel_two hm
    rw [hc, Item218Proof.padicValNat_ordG2 hm1] at hv
    have hkm : (2 ^ m) ^ 2 = 2 ^ (k + k) := by
      rw [← pow_mul]
      congr 1
      omega
    have hlt := three_mul_ordG2_lt (r := 2 ^ m) (Nat.le_self_pow (by omega : m ≠ 0) 2)
    rw [hkm] at hlt
    set P := (2 ^ (k + k)) ^ 3 * (((2 ^ (k + k)) ^ 2 - 1) * ((2 ^ (k + k)) ^ 3 - 1)) with hP
    set O := CFSG.Open.ordG2 (2 ^ m) with hO
    have hpos : 0 < O := hc ▸ Nat.card_pos
    rcases hcard with h | h <;> rw [hc] at h <;> omega
  ·
    have hm1 : 1 ≤ m := hm.1.2.1
    have hc : Nat.card (lBar X) = CFSG.Open.ordTrialityD4 (2 ^ m) :=
      Timmesfeld.card_chevalleyExceptionalModel_two hm
    rw [hc, Item218Proof.padicValNat_ordTrialityD4 hm1] at hv
    have hkm : (2 ^ m) ^ 4 = 2 ^ (k + k) := by
      rw [← pow_mul]
      congr 1
      omega
    have hlt := three_mul_ordTrialityD4_lt (r := 2 ^ m) (Nat.le_self_pow (by omega : m ≠ 0) 2)
    rw [hkm] at hlt
    set P := (2 ^ (k + k)) ^ 3 * (((2 ^ (k + k)) ^ 2 - 1) * ((2 ^ (k + k)) ^ 3 - 1)) with hP
    set O := CFSG.Open.ordTrialityD4 (2 ^ m) with hO
    have hpos : 0 < O := hc ▸ Nat.card_pos
    rcases hcard with h | h <;> rw [hc] at h <;> omega

end List

end Item218Res2Proof

end CFSG.RankThree.PartTwo.Sec21
