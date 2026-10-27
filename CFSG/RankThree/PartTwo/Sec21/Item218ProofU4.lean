module

public import CFSG.RankThree.PartTwo.Sec21.Item218Proof
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.RankThree.PartTwo.Sec21.Item22Tools
import CFSG.Sporadic.Mathieu.M24
import CFSG.Sporadic.He.Simple
import CFSG.Sporadic.Ru
import CFSG.Sporadic.J4
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item218Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSU)

theorem padicValNat_card_projSU_four {n : ℕ} (hn : 1 ≤ n) :
    padicValNat 2 (Nat.card (projSU 4 2 n)) = n * 6 := by
  rw [card_projSU le_rfl hn, ordTwistedA_three_eq hn,
    padicValNat_pow_two_pow_mul_odd (odd_ordTwistedA_three_part hn)]

theorem card_lBar_of_mulEquiv_projSU_four {G : Type} [Group G] {L : Subgroup G} {n : ℕ}
    (hn : 1 ≤ n) (e : L ≃* projSU 4 2 n) :
    Nat.card (lBar L) = 1 ∨ Nat.card (lBar L) = Nat.card (projSU 4 2 n) := by
  have : IsSimpleGroup (projSU 4 2 n) := isSimpleGroup_projSU le_rfl hn
  have hs : IsSimpleGroup L := e.isSimpleGroup
  rcases hs.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 L) with h | h
  · right
    change (aschbacherSolvableCore 3 L).index = _
    rw [h, Subgroup.index_bot, Nat.card_congr e.toEquiv]
  · left
    change (aschbacherSolvableCore 3 L).index = _
    rw [h, Subgroup.index_top]

theorem odd_pow_eight_add_pow_four_add_one {m : ℕ} (hm : 1 ≤ m) :
    Odd ((2 ^ m) ^ 8 + (2 ^ m) ^ 4 + 1) := by
  have h2 : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
  exact ((Nat.even_pow' (by norm_num)).mpr h2 |>.add
    ((Nat.even_pow' (by norm_num)).mpr h2)).add_one

theorem padicValNat_ordG2 {m : ℕ} (hm : 1 ≤ m) :
    padicValNat 2 (CFSG.Open.ordG2 (2 ^ m)) = m * 6 := by
  rw [CFSG.Open.ordG2, mul_assoc]
  exact padicValNat_pow_two_pow_mul_odd
    ((Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
      (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)))

theorem padicValNat_ordTrialityD4 {m : ℕ} (hm : 1 ≤ m) :
    padicValNat 2 (CFSG.Open.ordTrialityD4 (2 ^ m)) = m * 12 := by
  rw [CFSG.Open.ordTrialityD4, mul_assoc, mul_assoc]
  exact padicValNat_pow_two_pow_mul_odd ((odd_pow_eight_add_pow_four_add_one hm).mul
    ((Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
      (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))))

theorem ordG2_ne_card_projSU_four {n : ℕ} (hn : 1 ≤ n) :
    CFSG.Open.ordG2 (2 ^ n) ≠ Nat.card (projSU 4 2 n) := by
  rw [card_projSU le_rfl hn, ordTwistedA_three_eq hn, CFSG.Open.ordG2]
  intro hc
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set q := 2 ^ n with hqdef
  have hq1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq1
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
  have hcZ := congrArg (fun x : ℕ => (x : ℤ)) hc
  push_cast [Nat.cast_sub h2, Nat.cast_sub h4, Nat.cast_sub h6] at hcZ
  have hqZ : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hpos : 0 < (q : ℤ) ^ 6 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 3 * ((q : ℤ) - 1) *
      ((q : ℤ) ^ 3 + 1)) := by
    have ha : 0 < (q : ℤ) ^ 2 - 1 := by nlinarith
    have hb : 0 < (q : ℤ) - 1 := by linarith
    exact mul_pos (mul_pos (by positivity) ha) (mul_pos (mul_pos (by positivity) hb)
      (by positivity))
  have hzero : (q : ℤ) ^ 6 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 3 * ((q : ℤ) - 1) *
      ((q : ℤ) ^ 3 + 1)) = 0 := by
    linear_combination (-1 : ℤ) * hcZ
  linarith


theorem padicValNat_card_lBar_of_isList218
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsList218 L) :
    padicValNat 2 (Nat.card (lBar L)) = 10 ∨ padicValNat 2 (Nat.card (lBar L)) = 7 ∨
      padicValNat 2 (Nat.card (lBar L)) = 14 ∨ padicValNat 2 (Nat.card (lBar L)) = 21 ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card (lBar L) = CFSG.Open.ordG2 (2 ^ m) ∧
        padicValNat 2 (Nat.card (lBar L)) = m * 6) ∨
      ∃ m : ℕ, 1 ≤ m ∧ padicValNat 2 (Nat.card (lBar L)) = m * 12 := by
  rcases hL with hf | hf | hf | hf | hf | ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    rw [Nat.card_congr hf.some.toEquiv, Sporadic.Mathieu.card_M24,
      show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num,
      padicValNat_two_pow_mul_odd (by decide)]
  · left
    rw [Nat.card_congr hf.some.toEquiv, Sporadic.He.card_He,
      show (4030387200 : ℕ) = 2 ^ 10 * 3935925 by norm_num,
      padicValNat_two_pow_mul_odd (by decide)]
  · right; left
    rw [Nat.card_congr hf.some.toEquiv, KFacts.KS14.card_nativeJ2,
      show (604800 : ℕ) = 2 ^ 7 * 4725 by norm_num, padicValNat_two_pow_mul_odd (by decide)]
  · right; right; left
    rw [Nat.card_congr hf.some.toEquiv, Sporadic.Ru.card_Ru,
      show (145926144000 : ℕ) = 2 ^ 14 * 8906625 by norm_num,
      padicValNat_two_pow_mul_odd (by decide)]
  · right; right; right; left
    rw [Nat.card_congr hf.some.toEquiv, Sporadic.J4.card_J4,
      show (86775571046077562880 : ℕ) = 2 ^ 21 * 41377816699065 by norm_num,
      padicValNat_two_pow_mul_odd (by decide)]
  · right; right; right; right; left
    have hm1 : 1 ≤ m := hm.1.2.1
    have hc : Nat.card (lBar L) = CFSG.Open.ordG2 (2 ^ m) :=
      Timmesfeld.card_chevalleyExceptionalModel_two hm
    exact ⟨m, hm1, hc, by rw [hc, padicValNat_ordG2 hm1]⟩
  · right; right; right; right; right
    have hm1 : 1 ≤ m := hm.1.2.1
    have hc : Nat.card (lBar L) = CFSG.Open.ordTrialityD4 (2 ^ m) :=
      Timmesfeld.card_chevalleyExceptionalModel_two hm
    exact ⟨m, hm1, by rw [hc, padicValNat_ordTrialityD4 hm1]⟩

theorem kF218NotU4 :
    KF218NotU4 := by
  intro G _ _ L hL ⟨n, hn, ⟨e⟩⟩
  have hn1 : 1 ≤ n := hn.pos
  obtain ⟨k, hk⟩ := hn
  have hU := padicValNat_card_projSU_four hn1
  have hV := padicValNat_card_lBar_of_isList218 hL
  rcases card_lBar_of_mulEquiv_projSU_four hn1 e with h1 | hc
  · rw [h1, padicValNat_one_right] at hV
    rcases hV with h | h | h | h | ⟨m, hm, -, h⟩ | ⟨m, hm, h⟩ <;> omega
  · rw [hc, hU] at hV
    rcases hV with h | h | h | h | ⟨m, hm, hG, h⟩ | ⟨m, hm, h⟩
    · omega
    · omega
    · omega
    · omega
    · obtain rfl : m = n := by omega
      exact ordG2_ne_card_projSU_four hn1 hG.symm
    · omega

end CFSG.RankThree.PartTwo.Sec21.Item218Proof
