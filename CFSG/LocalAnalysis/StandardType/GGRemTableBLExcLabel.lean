module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLCover
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDE6Field
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwDFieldHolds
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwE6Field
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63R
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitCopTableB
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitFieldHolds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Final
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofFinal
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd
public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutUnit
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBLinIrredRound
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTBMain
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTvMain
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTvAMain
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63ActDesc
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Main
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActMain
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvRes
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvSix
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvSixQ2Descent
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvSixQ2Odd

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType


@[expose] def GGRemTableBLExcLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .E6 ∧ p = 3 ∧ (p ∣ 2 ^ lab.n - 1 ∨ lab.n = 1)) ∨
    ((lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ lab.n = 1 ∧ p = 3)

@[expose] def GGRemTableBLExc2Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .E6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n - 1) ∨
    ((lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ lab.n = 1 ∧ p = 3)

macro "ggRemExc_unfold" : tactic =>
  `(tactic| simp only [GGTypeALabel, GGReflSpLabel, GGCorFourTwoSmallLabel,
      TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel, GGStdSubSmallVacLabel,
      GGTableBTwDThreeLabel, GGB2derThreeLabel, GGCorFourTwoTableBMoreLabel, GGSpTwoThreeLabel,
      GGCorFourTwoTableBVacLabel, StdSubRestThree.GGTwoThreeSmallLabel, GGTableBNbrInnerA2Label,
      GGCorFourTwoOrthSplitLabel, GGCorFourTwoVacMoreLabel, GGOrthNsVacLabel, GGOrthNsLabel,
      GGCorFourTwoOpenVacLabel, GGUnitaryCoprimeLabel, GGExcLTableBLabel, GGExcLSplitLabel,
      GGExcLSplitE6Label, GGExcLLineAllLabel, GGLinDvdLabel, GGOrthLD4TwoLabel,
      GGUnitDvdCoprimeNLabel, GGLinTwoLabel, GGUnitDvd63CoprimeNLabel, GGUnitDvdLabelNo63,
      GGOrthLTwDFieldLabel, GGUnitCopFieldLabel, GGUnitDvd63Label, GGUnitDvdLabel,
      GGTwoThreeLabel, GGOrthLTvLabel, GGExcLVacLabel, GGExcLIDLabel, GGTwE6FieldLabel,
      GGE6ThreeFieldLabel, GGUnitDvd63FieldLabel, GGRemTableBLExcLabel, LargeEvenUntwisted,
      LargeEvenSplit, not_or, not_and, not_not, reduceCtorEq, true_and, and_true,
      false_and, and_false, true_or, or_true, false_or, or_false, not_true_eq_false,
      not_false_eq_true, true_implies, false_implies, implies_true, imp_false] at *)

@[expose] def GGRemTableBLExcResCx (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((((((GGRemainderTableBLResCx p lab ∧ ¬ GGUnitDvdCoprimeNLabel p lab) ∧
      ¬ GGLinTwoLabel p lab) ∧ ¬ GGUnitDvd63CoprimeNLabel p lab) ∧
      ¬ GGUnitDvdLabelNo63 p lab) ∧ ¬ GGOrthLTwDFieldLabel p lab) ∧
      ¬ GGUnitCopFieldLabel p lab) ∧ ¬ GGUnitDvd63Label p lab

@[expose] def GGRemTableBLExcResAct (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (((((((GGRemainderTableBLResAct p lab ∧ ¬ GGLinDvdLabel p lab) ∧
      ¬ GGUnitDvdCoprimeNLabel p lab) ∧ ¬ GGLinTwoLabel p lab) ∧
      ¬ GGUnitDvd63CoprimeNLabel p lab) ∧ ¬ GGUnitDvdLabelNo63 p lab) ∧
      ¬ GGOrthLTwDFieldLabel p lab) ∧ ¬ GGUnitCopFieldLabel p lab) ∧ ¬ GGUnitDvd63Label p lab

@[expose] def GGRemTableBLExcResTv (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((GGRemainderTableBLResTv p lab ∧ ¬ GGUnitaryTvResLabel p lab) ∧ ¬ GGLinTwoLabel p lab) ∧
    ¬ GGUnitDvd63Label p lab

@[expose] def GGRemTableBLExcResLine (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGRemainderTableBLResLine p lab ∧ ¬ GGUnitDvdLabel p lab ∧ ¬ GGLinTwoLabel p lab

@[expose] def GGRemTableBLExcResLID (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (((((GGRemainderTableBLResLID p lab ∧ ¬ GGUnitDvdLabelNo63 p lab) ∧
      ¬ GGTwE6FieldLabel p lab) ∧ ¬ GGE6ThreeFieldLabel p lab) ∧
      ¬ GGOrthLTwDFieldLabel p lab) ∧ ¬ GGUnitCopFieldLabel p lab) ∧
      ¬ GGUnitDvd63FieldLabel p lab

theorem ggRemTableBLExc_ne_two {p n : ℕ} (hn : 1 ≤ n) (h : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) :
    p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rcases h with h | h <;> omega

theorem ggRemTableBLExc_ne_two_of_split {p : ℕ} {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hS : LargeEvenSplit p lab) : p ≠ 2 := by
  obtain ⟨hn, -⟩ := hΛ
  rcases hS with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, rfl⟩
  · exact ggRemTableBLExc_ne_two hn (Or.inl h)
  · exact ggRemTableBLExc_ne_two hn (Or.inr h)
  · exact ggRemTableBLExc_ne_two hn (Or.inl h)
  · norm_num

theorem ggRemTableBLExc_dvd_sq_sub {p n : ℕ} (h : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) :
    p ∣ (2 ^ n) ^ 2 - 1 := by
  have hm : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have key : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring
  rw [key]
  rcases h with h | h
  · exact Dvd.dvd.mul_right h _
  · exact Dvd.dvd.mul_left h _

theorem ggRemTableBLExcResCx_of_act {p : ℕ} {lab : LargeEvenLabel}
    (h : GGRemTableBLExcResAct p lab) : GGRemTableBLExcResCx p lab := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hA, hNLin⟩, hUDCN⟩, hLT2⟩, hUD63CN⟩, hUDNo63⟩, hOLT⟩, hUCF⟩, hUD63⟩ := h
  obtain ⟨hR12, hNLD4⟩ := hA
  unfold GGRemTableBLExcResCx GGRemainderTableBLResCx
  exact ⟨⟨⟨⟨⟨⟨⟨⟨hR12, fun h1 => h1.elim hNLin hNLD4⟩, hUDCN⟩, hLT2⟩, hUD63CN⟩, hUDNo63⟩, hOLT⟩,
    hUCF⟩, hUD63⟩

theorem ggRemTableBLExc_of_resCx {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hΛ : LargeEvenInLambda2 lab) (hS : LargeEvenSplit p lab)
    (h : GGRemTableBLExcResCx p lab) : GGRemTableBLExcLabel p lab := by
  have hp2 := ggRemTableBLExc_ne_two_of_split hΛ hS
  have hd1 : ¬ p ∣ 1 := fun h1 => hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hd2 : ¬ p ∣ 2 := fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hd3 : p ∣ 3 ↔ p = 3 := Nat.prime_dvd_prime_iff_eq hp Nat.prime_three
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨⟨⟨⟨⟨⟨⟨hR, hUDCN⟩, hLT2⟩, hUD63CN⟩, hUDNo63⟩, hOLT⟩, hUCF⟩, hUD63⟩ := h
  obtain ⟨hR12, hNLD⟩ := hR
  have hNLin : ¬ GGLinDvdLabel p ⟨tag, rank, n⟩ := fun h1 => hNLD (Or.inl h1)
  have hNLD4 : ¬ GGOrthLD4TwoLabel p ⟨tag, rank, n⟩ := fun h1 => hNLD (Or.inr h1)
  obtain ⟨hR11, hNExc⟩ := hR12
  obtain ⟨hV3, hNOrth⟩ := hR11
  obtain ⟨hR2, hNVac⟩ := hV3
  obtain ⟨hRT, hNTBM⟩ := hR2
  obtain ⟨hOL, hNUCOV⟩ := hRT
  obtain ⟨hRS, hNSmall⟩ := hOL
  obtain ⟨hRest, hNRefl, -⟩ := hRS
  have hNTA : ¬ GGTypeALabel p ⟨tag, rank, n⟩ := hRest
  cases tag
  case A =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      by_cases h1 : p ∣ 2 ^ n - 1
      · by_cases h3 : 3 ≤ rank
        · simp_all <;> omega
        · have hr' : rank = 1 ∨ rank = 2 := by omega
          rcases hr' with rfl | rfl <;> simp_all <;> omega
      · rcases hS with h | ⟨rfl, rfl⟩
        · exact absurd h h1
        · by_cases h5 : rank ≤ 4
          · simp_all <;> omega
          · have h6 : 5 ≤ rank := by omega
            simp_all
  case twA =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      have hD2 : p ∣ 2 ^ n + 1 := by
        rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
      by_cases h2 : rank = 2
      · simp_all <;> omega
      · have hr3 : 3 ≤ rank := by omega
        by_cases h3 : p ∣ rank + 1
        · by_cases h5 : rank = 5 ∧ p = 3
          · simp_all <;> omega
          · simp_all <;> omega
        · by_cases hn3 : p ∣ n
          · simp_all <;> omega
          · simp_all <;> omega
  case B =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case C =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case D =>
    obtain ⟨hn, hr⟩ := hΛ
    ggRemExc_unfold
    all_goals
      by_cases h3 : rank = 3
      · subst h3
        rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
      · have h4 : 4 ≤ rank := by omega
        rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case twD =>
    obtain ⟨hn, hr⟩ := hΛ
    ggRemExc_unfold
    all_goals
      have hD : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
        rcases hS with h | h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
      by_cases h2 : rank = 2
      · subst h2
        have hsq := ggRemTableBLExc_dvd_sq_sub hD
        simp_all
      · by_cases h3 : rank = 3
        · subst h3
          rcases hD with h | h
          · simp_all <;> omega
          · by_cases hn3 : p ∣ n <;> simp_all <;> omega
        · have hr4 : 4 ≤ rank := by omega
          rcases hD with h | h
          · simp_all <;> omega
          · by_cases hn3 : p ∣ n <;> simp_all <;> omega
  case twE6 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case E6 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      by_cases hp3 : p = 3
      · subst hp3
        rcases hS with h | ⟨rfl, -⟩ <;> simp_all <;> omega
      · rcases hS with h | ⟨-, rfl⟩
        · simp_all <;> omega
        · exact absurd rfl hp3
  case E7 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case E8 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case F4 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case triD4 =>
    ggRemExc_unfold
    all_goals simp_all
  case G2 =>
    ggRemExc_unfold
    all_goals simp_all
  case twB2 =>
    ggRemExc_unfold
    all_goals simp_all
  case twF4 =>
    obtain ⟨hn, hr0, -, hn3⟩ := hΛ
    ggRemExc_unfold
    all_goals
      by_cases hp3 : p = 3 <;> simp_all <;> omega
  case B2der =>
    obtain ⟨hn, hr0, rfl⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨-, rfl⟩ <;> simp_all <;> omega
  case G2der =>
    ggRemExc_unfold
    all_goals simp_all
  case twF4der =>
    ggRemExc_unfold
    all_goals simp_all

theorem ggRemTableBLExc_of_resTv {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hΛ : LargeEvenInLambda2 lab) (hS : LargeEvenSplit p lab)
    (h : GGRemTableBLExcResTv p lab) : GGRemTableBLExcLabel p lab := by
  have hp2 := ggRemTableBLExc_ne_two_of_split hΛ hS
  have hd1 : ¬ p ∣ 1 := fun h1 => hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hd2 : ¬ p ∣ 2 := fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hd3 : p ∣ 3 ↔ p = 3 := Nat.prime_dvd_prime_iff_eq hp Nat.prime_three
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨⟨⟨hTv, hNUT⟩, hNLT2⟩, hNUD63⟩ := h
  have hNUT' : tag = LargeEvenLieTag.twA → ¬ (rank = 5 ∧ p = 3) → False :=
    fun ht hr => hNUT (by unfold GGUnitaryTvResLabel; exact ⟨hTv, ht, hr⟩)
  obtain ⟨hR12, hNSO⟩ := hTv
  have hNSp : ¬ GGSpTwoThreeLabel p ⟨tag, rank, n⟩ := fun h1 => hNSO (Or.inl (Or.inl h1))
  have hNOLT : ¬ GGOrthLTvLabel p ⟨tag, rank, n⟩ := fun h1 => hNSO (Or.inl (Or.inr h1))
  have hNLin : ¬ GGLinDvdLabel p ⟨tag, rank, n⟩ := fun h1 => hNSO (Or.inr h1)
  obtain ⟨hR3, hNExc⟩ := hR12
  obtain ⟨hOL, hNVac⟩ := hR3
  obtain ⟨hRS, hNSmall⟩ := hOL
  obtain ⟨hRest, hNRefl, -⟩ := hRS
  have hNTA : ¬ GGTypeALabel p ⟨tag, rank, n⟩ := hRest
  cases tag
  case A =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      by_cases h1 : p ∣ 2 ^ n - 1
      · by_cases h3 : 3 ≤ rank
        · simp_all <;> omega
        · have hr' : rank = 1 ∨ rank = 2 := by omega
          rcases hr' with rfl | rfl <;> simp_all <;> omega
      · rcases hS with h | ⟨rfl, rfl⟩
        · exact absurd h h1
        · by_cases h5 : rank ≤ 4
          · simp_all <;> omega
          · have h6 : 5 ≤ rank := by omega
            simp_all
  case twA =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      have hD2 : p ∣ 2 ^ n + 1 := by
        rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
      by_cases h2 : rank = 2
      · simp_all <;> omega
      · have hr3 : 3 ≤ rank := by omega
        by_cases h5 : rank = 5 ∧ p = 3
        · simp_all <;> omega
        · simp_all <;> omega
  case B =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case C =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case D =>
    obtain ⟨hn, hr⟩ := hΛ
    ggRemExc_unfold
    all_goals
      have h4 : 3 ≤ rank := hr
      by_cases h3 : rank = 3
      · subst h3
        rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
      · have h4' : 4 ≤ rank := by omega
        rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case twD =>
    obtain ⟨hn, hr⟩ := hΛ
    ggRemExc_unfold
    all_goals
      have hD : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
        rcases hS with h | h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
      by_cases h2 : rank = 2
      · subst h2
        have hsq := ggRemTableBLExc_dvd_sq_sub hD
        simp_all
      · by_cases h3 : rank = 3
        · subst h3
          rcases hD with h | h <;> simp_all <;> omega
        · have hr4 : 4 ≤ rank := by omega
          rcases hD with h | h <;> simp_all <;> omega
  case twE6 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case E6 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      by_cases hp3 : p = 3
      · subst hp3
        rcases hS with h | ⟨rfl, -⟩ <;> simp_all <;> omega
      · rcases hS with h | ⟨-, rfl⟩
        · simp_all <;> omega
        · exact absurd rfl hp3
  case E7 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case E8 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case F4 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case triD4 =>
    ggRemExc_unfold
    all_goals simp_all
  case G2 =>
    ggRemExc_unfold
    all_goals simp_all
  case twB2 =>
    ggRemExc_unfold
    all_goals simp_all
  case twF4 =>
    obtain ⟨hn, hr0, -, hn3⟩ := hΛ
    ggRemExc_unfold
    all_goals
      by_cases hp3 : p = 3 <;> simp_all <;> omega
  case B2der =>
    obtain ⟨hn, hr0, rfl⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨-, rfl⟩ <;> simp_all <;> omega
  case G2der =>
    ggRemExc_unfold
    all_goals simp_all
  case twF4der =>
    ggRemExc_unfold
    all_goals simp_all

theorem ggRemTableBLExc_of_resLine {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hΛ : LargeEvenInLambda2 lab) (hS : LargeEvenSplit p lab)
    (h : GGRemTableBLExcResLine p lab) : GGRemTableBLExcLabel p lab := by
  have hp2 := ggRemTableBLExc_ne_two_of_split hΛ hS
  have hd1 : ¬ p ∣ 1 := fun h1 => hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hd2 : ¬ p ∣ 2 := fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hd3 : p ∣ 3 ↔ p = 3 := Nat.prime_dvd_prime_iff_eq hp Nat.prime_three
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hLine, hNUDL, hNLT2⟩ := h
  obtain ⟨hR12, hNLS⟩ := hLine
  have hNLin : ¬ GGLinDvdLabel p ⟨tag, rank, n⟩ := fun h1 => hNLS (Or.inl h1)
  have hNSp : ¬ GGSpTwoThreeLabel p ⟨tag, rank, n⟩ := fun h1 => hNLS (Or.inr h1)
  obtain ⟨hR11, hNExc⟩ := hR12
  obtain ⟨hR3, hNOrth⟩ := hR11
  obtain ⟨hLR, hNVac⟩ := hR3
  obtain ⟨hOL, hNOS, hNUC⟩ := hLR
  obtain ⟨hRS, hNSmall⟩ := hOL
  obtain ⟨hRest, hNRefl, -⟩ := hRS
  have hNTA : ¬ GGTypeALabel p ⟨tag, rank, n⟩ := hRest
  cases tag
  case A =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      by_cases h1 : p ∣ 2 ^ n - 1
      · by_cases h3 : 3 ≤ rank
        · simp_all <;> omega
        · have hr' : rank = 1 ∨ rank = 2 := by omega
          rcases hr' with rfl | rfl <;> simp_all <;> omega
      · rcases hS with h | ⟨rfl, rfl⟩
        · exact absurd h h1
        · by_cases h5 : rank ≤ 4
          · simp_all <;> omega
          · have h6 : 5 ≤ rank := by omega
            simp_all
  case twA =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      have hD2 : p ∣ 2 ^ n + 1 := by
        rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
      by_cases h2 : rank = 2
      · simp_all <;> omega
      · have hr3 : 3 ≤ rank := by omega
        by_cases h3 : p ∣ rank + 1
        · simp_all <;> omega
        · simp_all <;> omega
  case B =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case C =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case D =>
    obtain ⟨hn, hr⟩ := hΛ
    ggRemExc_unfold
    all_goals
      by_cases h3 : rank = 3
      · subst h3
        rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
      · have h4 : 4 ≤ rank := by omega
        rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case twD =>
    obtain ⟨hn, hr⟩ := hΛ
    ggRemExc_unfold
    all_goals
      have hD : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
        rcases hS with h | h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
      by_cases h2 : rank = 2
      · subst h2
        have hsq := ggRemTableBLExc_dvd_sq_sub hD
        simp_all
      · by_cases h3 : rank = 3
        · subst h3
          rcases hD with h | h <;> simp_all <;> omega
        · have hr4 : 4 ≤ rank := by omega
          rcases hD with h | h <;> simp_all <;> omega
  case twE6 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case E6 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      by_cases hp3 : p = 3
      · subst hp3
        rcases hS with h | ⟨rfl, -⟩ <;> simp_all <;> omega
      · rcases hS with h | ⟨-, rfl⟩
        · simp_all <;> omega
        · exact absurd rfl hp3
  case E7 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case E8 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case F4 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case triD4 =>
    ggRemExc_unfold
    all_goals simp_all
  case G2 =>
    ggRemExc_unfold
    all_goals simp_all
  case twB2 =>
    ggRemExc_unfold
    all_goals simp_all
  case twF4 =>
    obtain ⟨hn, hr0, -, hn3⟩ := hΛ
    ggRemExc_unfold
    all_goals
      by_cases hp3 : p = 3 <;> simp_all <;> omega
  case B2der =>
    obtain ⟨hn, hr0, rfl⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨-, rfl⟩ <;> simp_all <;> omega
  case G2der =>
    ggRemExc_unfold
    all_goals simp_all
  case twF4der =>
    ggRemExc_unfold
    all_goals simp_all

theorem ggRemTableBLExc_resLID_false {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hΛ : LargeEvenInLambda2 lab) (hS : LargeEvenSplit p lab)
    (h : GGRemTableBLExcResLID p lab) : False := by
  have hp2 := ggRemTableBLExc_ne_two_of_split hΛ hS
  have hd1 : ¬ p ∣ 1 := fun h1 => hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hd2 : ¬ p ∣ 2 := fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hd3 : p ∣ 3 ↔ p = 3 := Nat.prime_dvd_prime_iff_eq hp Nat.prime_three
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨⟨⟨⟨⟨⟨hLID, hNUDNo63⟩, hNTwE6F⟩, hNE6F⟩, hNOLT⟩, hNUCF⟩, hNUD63F⟩ := h
  obtain ⟨hR12, hNLLD⟩ := hLID
  have hNLin : ¬ GGLinDvdLabel p ⟨tag, rank, n⟩ := fun h1 => hNLLD (Or.inl h1)
  have hNLD4 : ¬ GGOrthLD4TwoLabel p ⟨tag, rank, n⟩ := fun h1 => hNLLD (Or.inr h1)
  obtain ⟨hR3, hNExcL⟩ := hR12
  obtain ⟨hLR, hNVac⟩ := hR3
  obtain ⟨hLL, hNOS, hNOV⟩ := hLR
  obtain ⟨hRL, hNSmall⟩ := hLL
  obtain ⟨hRS, hNTT, hNSpTT⟩ := hRL
  obtain ⟨hRest, hNRefl, -⟩ := hRS
  have hNTA : ¬ GGTypeALabel p ⟨tag, rank, n⟩ := hRest
  cases tag
  case A =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩
      · by_cases h3 : 3 ≤ rank
        · simp_all <;> omega
        · have hr' : rank = 1 ∨ rank = 2 := by omega
          rcases hr' with rfl | rfl <;> simp_all <;> omega
      · simp_all <;> omega
  case twA =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      have hD2 : p ∣ 2 ^ n + 1 := by
        rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
      by_cases h2 : rank = 2
      · simp_all <;> omega
      · have hr3 : 3 ≤ rank := by omega
        by_cases hn3 : p ∣ n
        · by_cases h3 : p ∣ rank + 1
          · by_cases h5 : rank = 5 ∧ p = 3
            · simp_all <;> omega
            · simp_all <;> omega
          · simp_all <;> omega
        · simp_all <;> omega
  case twD =>
    obtain ⟨hn, hr⟩ := hΛ
    ggRemExc_unfold
    all_goals
      have hD : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
        rcases hS with h | h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
      by_cases h2 : rank = 2
      · subst h2
        have hsq := ggRemTableBLExc_dvd_sq_sub hD
        simp_all
      · by_cases h3 : rank = 3
        · subst h3
          rcases hD with h | h
          · simp_all <;> omega
          · by_cases hn3 : p ∣ n <;> simp_all <;> omega
        · have hr4 : 4 ≤ rank := by omega
          rcases hD with h | h
          · simp_all <;> omega
          · by_cases hn3 : p ∣ n <;> simp_all <;> omega
  case twE6 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      have hD2 : p ∣ 2 ^ n + 1 := by
        rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
      by_cases hn3 : p ∣ n <;> simp_all <;> omega
  case E6 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      by_cases hp3 : p = 3
      · subst hp3
        by_cases hn3 : 3 ∣ n
        · rcases hS with h | ⟨rfl, -⟩ <;> simp_all <;> omega
        · simp_all <;> omega
      · rcases hS with h | ⟨-, rfl⟩
        · simp_all <;> omega
        · exact absurd rfl hp3
  case E7 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case E8 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case F4 =>
    obtain ⟨hn, hr0⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case triD4 =>
    ggRemExc_unfold
    all_goals simp_all
  case G2 =>
    ggRemExc_unfold
    all_goals simp_all
  case twB2 =>
    ggRemExc_unfold
    all_goals simp_all
  case twF4 =>
    obtain ⟨hn, hr0, -, hn3⟩ := hΛ
    ggRemExc_unfold
    all_goals
      by_cases hp3 : p = 3 <;> simp_all <;> omega
  case B =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case C =>
    obtain ⟨hn, hr, -⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
  case D =>
    obtain ⟨hn, hr⟩ := hΛ
    ggRemExc_unfold
    all_goals
      by_cases h3 : rank = 3
      · subst h3
        rcases hS with h | ⟨rfl, rfl⟩ <;> simp_all <;> omega
      · have h4 : 4 ≤ rank := by omega
        rcases hS with h | ⟨rfl, rfl⟩
        · simp_all <;> omega
        · by_cases h5 : rank = 4
          · simp_all <;> omega
          · have h6 : 5 ≤ rank := by omega
            simp_all
  case B2der =>
    obtain ⟨hn, hr0, rfl⟩ := hΛ
    ggRemExc_unfold
    all_goals
      rcases hS with h | ⟨-, rfl⟩ <;> simp_all <;> omega
  case G2der =>
    ggRemExc_unfold
    all_goals simp_all
  case twF4der =>
    ggRemExc_unfold
    all_goals simp_all

end CFSG.Yardstones.M3f9567aba59d
