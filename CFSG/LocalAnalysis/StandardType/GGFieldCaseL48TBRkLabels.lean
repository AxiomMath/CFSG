module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkNarrowDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridgeLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoTableB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48_irred_labels_exhaustive {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (hs : LargeEvenSplit p lab) (hv : ¬ GGL48TableBVacLabel p lab)
    (hd : ¬ GGD4Three p lab) (hf : ¬ GGL48F4TwoThreeLabel p lab) (ht : ¬ GGL48TB0TwRow p lab) :
    (GGTypeALabel p lab ∨ GGTableBNbrInnerExcSplitLabel p lab ∨ GGTableBF4Label p lab ∨
      GGCorFourTwoOrthSplitLabel p lab ∨ GGE6TwoThreeLabel p lab ∨ GGUnitaryCoprimeLabel p lab ∨
      GGSpNonsplitLabel p lab ∨ GGOrthNsLabel p lab ∨ TableBExcTwoTB.GGE7TwoThreeLabel p lab ∨
      TableBExcTwoTB.GGE8TwoThreeLabel p lab) ∨
    GGTableBSympLabel p lab ∨ GGTableBNbrInnerLinearNsLabel p lab ∨ GGL48IrredOpenLabel p lab := by
  obtain ⟨t, l, n⟩ := lab
  simp only [GGL48TableBVacLabel, GGCorFourTwoSmallLabel,
    TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel, GGStdSubSmallVacLabel,
    GGTableBTwDThreeLabel, GGB2derThreeLabel, StdSubRestThree.GGTwoThreeSmallLabel,
    GGLinearTwoLabel] at hv
  cases t
  case A =>
    simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hlab hs
    simp at hs hv
    obtain ⟨hA1, -, -⟩ := hv
    rcases hs with hq1 | ⟨hn1, hp3⟩
    · by_cases hdiv : p ∣ l + 1
      · have h : GGL48IrredOpenLabel p ⟨.A, l, n⟩ := Or.inr (Or.inl ⟨rfl, hdiv, hq1⟩)
        simp only [h, or_true, true_or]
      · have h : GGTypeALabel p ⟨.A, l, n⟩ := Or.inl ⟨rfl, hq1, hdiv⟩
        simp only [h, or_true, true_or]
    · have h4 : 4 ≤ l := by have := hA1 hp3 hn1; omega
      have hnot1 : ¬ p ∣ 2 ^ n - 1 := by rw [hn1, hp3]; norm_num
      have hp2 : p ≠ 2 := by omega
      have h : GGTableBNbrInnerLinearNsLabel p ⟨.A, l, n⟩ := ⟨rfl, h4, hp2, hnot1⟩
      simp only [h, or_true, true_or]
  case twA =>
    simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hlab hs
    simp at hs
    have hq2 : p ∣ 2 ^ n + 1 := by
      rcases hs with h | ⟨hn1, hp3⟩
      · exact h
      · rw [hn1, hp3]; norm_num
    by_cases hdiv : p ∣ l + 1
    · exact (ht (Or.inl ⟨rfl, hdiv, hq2⟩)).elim
    · have h : GGUnitaryCoprimeLabel p ⟨.twA, l, n⟩ := Or.inl ⟨rfl, hq2, hdiv⟩
      simp only [h, or_true, true_or]
  case B =>
    simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hlab hs
    simp at hs
    rcases hs with hq1 | ⟨hn1, hp3⟩
    · have h : GGTableBSympLabel p ⟨.B, l, n⟩ := ⟨Or.inl rfl, hq1⟩
      simp only [h, or_true, true_or]
    · have hq2 : p ∣ 2 ^ n + 1 := by rw [hn1, hp3]; norm_num
      have h : GGSpNonsplitLabel p ⟨.B, l, n⟩ := ⟨Or.inl rfl, hq2⟩
      simp only [h, or_true, true_or]
  case C =>
    simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hlab hs
    simp at hs
    rcases hs with hq1 | ⟨hn1, hp3⟩
    · have h : GGTableBSympLabel p ⟨.C, l, n⟩ := ⟨Or.inr rfl, hq1⟩
      simp only [h, or_true, true_or]
    · have hq2 : p ∣ 2 ^ n + 1 := by rw [hn1, hp3]; norm_num
      have h : GGSpNonsplitLabel p ⟨.C, l, n⟩ := ⟨Or.inr rfl, hq2⟩
      simp only [h, or_true, true_or]
  case D =>
    simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hlab hs
    simp at hs hv
    obtain ⟨hn, hl3⟩ := hlab
    rcases hs with hq1 | ⟨hn1, hp3⟩
    · by_cases hl : l = 3
      · have h : GGTypeALabel p ⟨.D, l, n⟩ := Or.inr (Or.inl ⟨rfl, hl, hq1⟩)
        simp only [h, or_true, true_or]
      · have h4 : 4 ≤ l := by omega
        have h : GGCorFourTwoOrthSplitLabel p ⟨.D, l, n⟩ := ⟨Or.inl rfl, h4, hq1⟩
        simp only [h, or_true, true_or]
    · have hlne : l ≠ 3 := hv hp3 hn1
      have h4 : 4 ≤ l := by omega
      have hq2 : p ∣ 2 ^ n + 1 := by rw [hn1, hp3]; norm_num
      have h : GGOrthNsLabel p ⟨.D, l, n⟩ := ⟨Or.inl rfl, h4, hq2⟩
      simp only [h, or_true, true_or]
  case twD =>
    simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hlab hs
    simp at hs hv
    obtain ⟨hn, hl2⟩ := hlab
    obtain ⟨hv13, hvne2⟩ := hv
    rcases hs with hq2 | hq1 | ⟨hn1, hp3⟩
    · by_cases hl3 : l = 3
      · have h : GGUnitaryCoprimeLabel p ⟨.twD, l, n⟩ := Or.inr ⟨rfl, hl3, hq2⟩
        simp only [h, or_true, true_or]
      · have h4 : 4 ≤ l := by omega
        have h : GGOrthNsLabel p ⟨.twD, l, n⟩ := ⟨Or.inr rfl, h4, hq2⟩
        simp only [h, or_true, true_or]
    · have hlne : l ≠ 3 := fun h => hv13 h hq1
      have h4 : 4 ≤ l := by omega
      have h : GGCorFourTwoOrthSplitLabel p ⟨.twD, l, n⟩ := ⟨Or.inr rfl, h4, hq1⟩
      simp only [h, or_true, true_or]
    · have h3 : 3 ≤ l := by omega
      by_cases hl3 : l = 3
      · have hq2' : p ∣ 2 ^ n + 1 := by rw [hn1, hp3]; norm_num
        have h : GGUnitaryCoprimeLabel p ⟨.twD, l, n⟩ := Or.inr ⟨rfl, hl3, hq2'⟩
        simp only [h, or_true, true_or]
      · have h4 : 4 ≤ l := by omega
        have hq2' : p ∣ 2 ^ n + 1 := by rw [hn1, hp3]; norm_num
        have h : GGOrthNsLabel p ⟨.twD, l, n⟩ := ⟨Or.inr rfl, h4, hq2'⟩
        simp only [h, or_true, true_or]
  case E6 =>
    simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hlab hs
    simp at hs
    rcases hs with hq1 | ⟨hn1, hp3⟩
    · by_cases hp3' : p = 3
      · have h3 : 3 ∣ 2 ^ n - 1 := by rw [← hp3']; exact hq1
        have h : GGL48IrredOpenLabel p ⟨.E6, l, n⟩ := Or.inr (Or.inr ⟨rfl, hp3', h3⟩)
        simp only [h, or_true, true_or]
      · have h : GGTableBNbrInnerExcSplitLabel p ⟨.E6, l, n⟩ := ⟨Or.inl ⟨rfl, hp3'⟩, hq1⟩
        simp only [h, or_true, true_or]
    · have h : GGE6TwoThreeLabel p ⟨.E6, l, n⟩ := ⟨rfl, hn1, hp3⟩
      simp only [h, or_true, true_or]
  case E7 =>
    simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hlab hs
    simp at hs
    rcases hs with hq1 | ⟨hn1, hp3⟩
    · have h : GGTableBNbrInnerExcSplitLabel p ⟨.E7, l, n⟩ := ⟨Or.inr (Or.inl rfl), hq1⟩
      simp only [h, or_true, true_or]
    · have h : TableBExcTwoTB.GGE7TwoThreeLabel p ⟨.E7, l, n⟩ := ⟨rfl, hn1, hp3⟩
      simp only [h, or_true, true_or]
  case E8 =>
    simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hlab hs
    simp at hs
    rcases hs with hq1 | ⟨hn1, hp3⟩
    · have h : GGTableBNbrInnerExcSplitLabel p ⟨.E8, l, n⟩ := ⟨Or.inr (Or.inr rfl), hq1⟩
      simp only [h, or_true, true_or]
    · have h : TableBExcTwoTB.GGE8TwoThreeLabel p ⟨.E8, l, n⟩ := ⟨rfl, hn1, hp3⟩
      simp only [h, or_true, true_or]
  case F4 =>
    simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hlab hs
    simp at hs
    rcases hs with hq1 | ⟨hn1, hp3⟩
    · have h : GGTableBF4Label p ⟨.F4, l, n⟩ := ⟨rfl, hq1⟩
      simp only [h, or_true, true_or]
    · exact (hf ⟨rfl, hn1, hp3⟩).elim
  case twE6 =>
    simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hlab hs
    simp at hs
    have hn : 1 ≤ n := hlab.1
    have hq2 : p ∣ 2 ^ n + 1 := by
      rcases hs with h | ⟨hn1, hp3⟩
      · exact h
      · rw [hn1, hp3]; norm_num
    by_cases hp3 : p = 3
    · exact (ht (Or.inr ⟨rfl, hp3, by simpa [hp3] using hq2⟩)).elim
    · have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hq2
      have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
      have h : GGL48IrredOpenLabel p ⟨.twE6, l, n⟩ := Or.inl ⟨rfl, hp5⟩
      simp only [h, or_true, true_or]
  case triD4 =>
    exfalso
    simpa using hv
  case G2 =>
    exfalso
    simpa using hv
  case twB2 =>
    exfalso
    simpa using hv
  case twF4 =>
    exfalso
    simpa using hv
  case B2der =>
    simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hlab hs
    simp at hs hv
    obtain ⟨-, -, hn1⟩ := hlab
    rcases hs with h1 | ⟨-, hp3⟩
    · have hp1 : p = 1 := by simpa [hn1] using h1
      exact (hp.ne_one hp1).elim
    · exact (hv hp3).elim
  case G2der =>
    exfalso
    simpa using hv
  case twF4der =>
    exfalso
    simpa using hv

end CFSG.StandardType
