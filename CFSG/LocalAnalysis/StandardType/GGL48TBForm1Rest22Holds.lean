module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenTwoThreeNarrow22Defs
import CFSG.LocalAnalysis.StandardType.GGCoverPOmegaMinusField

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private lemma false_of_tag_A {p l n : ℕ} (hΛ : LargeEvenInLambda2 ⟨.A, l, n⟩)
    (hS : LargeEvenSplit p ⟨.A, l, n⟩) (hVac : ¬ GGL48TableBVacLabel p ⟨.A, l, n⟩)
    (hA : ¬ GGL48TBTypeARow p ⟨.A, l, n⟩) (h2A : ¬ GGL48TBTwoARow p ⟨.A, l, n⟩) :
    False := by
  simp only [GGL48TableBVacLabel, GGCorFourTwoSmallLabel,
    TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel, GGStdSubSmallVacLabel,
    GGTableBTwDThreeLabel, GGB2derThreeLabel, StdSubRestThree.GGTwoThreeSmallLabel,
    GGLinearTwoLabel] at hVac
  simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hΛ hS
  simp at hS hVac
  obtain ⟨-, hne2, hne1⟩ := hVac
  obtain ⟨-, hl1, -⟩ := hΛ
  have hl3 : 3 ≤ l := by omega
  rcases hS with hq1 | ⟨hn1, hp3⟩
  · exact (hA ⟨rfl, hl3, hq1⟩).elim
  · exact (h2A ⟨rfl, hl3, hn1, hp3⟩).elim

private lemma false_of_tag_twA {p l n : ℕ} (hΛ : LargeEvenInLambda2 ⟨.twA, l, n⟩)
    (hS : LargeEvenSplit p ⟨.twA, l, n⟩) (hVac : ¬ GGL48TableBVacLabel p ⟨.twA, l, n⟩)
    (h0 : ¬ GGL48TB0TwRow p ⟨.twA, l, n⟩) (htA : ¬ GGL48TBTwistedARow p ⟨.twA, l, n⟩)
    (hU4 : ¬ GGL48TBUFourRow p ⟨.twA, l, n⟩) : False := by
  simp only [GGL48TableBVacLabel, GGCorFourTwoSmallLabel,
    TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel, GGStdSubSmallVacLabel,
    GGTableBTwDThreeLabel, GGB2derThreeLabel, StdSubRestThree.GGTwoThreeSmallLabel,
    GGLinearTwoLabel] at hVac
  simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hΛ hS
  simp at hS
  obtain ⟨-, hl2, -⟩ := hΛ
  have hlne2 : l ≠ 2 := by
    intro hl2'
    exact hVac (by simp [GGL48TableBVacLabel, hl2'])
  have hl3 : 3 ≤ l := by omega
  have hq2 : p ∣ 2 ^ n + 1 := by
    rcases hS with h | ⟨hn1, hp3⟩
    · exact h
    · rw [hn1, hp3]; norm_num
  by_cases hl3' : l = 3
  · exact (hU4 ⟨Or.inl rfl, hl3', hq2⟩).elim
  · have hl4 : 4 ≤ l := by omega
    by_cases hdiv : p ∣ l + 1
    · exact (h0 (Or.inl ⟨rfl, hdiv, hq2⟩)).elim
    · exact (htA ⟨rfl, hl4, hq2, hdiv⟩).elim

private lemma false_of_tag_B {p l n : ℕ} (hp : p.Prime)
    (hS : LargeEvenSplit p ⟨.B, l, n⟩) (hIn : ¬ GGL48TBForm1InnerRow p ⟨.B, l, n⟩)
    (hSp : ¬ GGTableBSympLabel p ⟨.B, l, n⟩) : False := by
  simp only [LargeEvenUntwisted, LargeEvenSplit] at hS
  simp at hS
  rcases hS with hq1 | ⟨hn1, hp3⟩
  · exact (hSp ⟨Or.inl rfl, hq1⟩).elim
  · subst hn1; subst hp3
    exact (hIn ⟨hp.not_dvd_one, Or.inl rfl⟩).elim

private lemma false_of_tag_C {p l n : ℕ} (hp : p.Prime)
    (hS : LargeEvenSplit p ⟨.C, l, n⟩) (hIn : ¬ GGL48TBForm1InnerRow p ⟨.C, l, n⟩)
    (hSp : ¬ GGTableBSympLabel p ⟨.C, l, n⟩) : False := by
  simp only [LargeEvenUntwisted, LargeEvenSplit] at hS
  simp at hS
  rcases hS with hq1 | ⟨hn1, hp3⟩
  · exact (hSp ⟨Or.inr rfl, hq1⟩).elim
  · subst hn1; subst hp3
    exact (hIn ⟨hp.not_dvd_one, Or.inr (Or.inl rfl)⟩).elim

private lemma false_of_tag_D {p l n : ℕ} (hΛ : LargeEvenInLambda2 ⟨.D, l, n⟩)
    (hS : LargeEvenSplit p ⟨.D, l, n⟩) (hVac : ¬ GGL48TableBVacLabel p ⟨.D, l, n⟩)
    (hD3 : ¬ GGL48TBDThreeRow p ⟨.D, l, n⟩) (hIn : ¬ GGL48TBForm1InnerRow p ⟨.D, l, n⟩)
    (hO : ¬ GGTableBOrthSplitLabel p ⟨.D, l, n⟩) : False := by
  simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hΛ hS
  simp at hS
  obtain ⟨-, hl3⟩ := hΛ
  rcases hS with hq1 | ⟨hn1, hp3⟩
  · by_cases hl : l = 3
    · exact (hD3 ⟨rfl, hl, hq1⟩).elim
    · have hl4 : 4 ≤ l := by omega
      exact (hO ⟨Or.inl rfl, hl4, hq1⟩).elim
  · by_cases hl : l = 3
    · subst hn1; subst hp3
      exfalso
      exact hVac (by
        simp [GGL48TableBVacLabel, StdSubRestThree.GGTwoThreeSmallLabel, hl])
    · have hl4 : 4 ≤ l := by omega
      have hpn : ¬ p ∣ n := by rw [hn1, hp3]; norm_num
      exact (hIn ⟨hpn, Or.inr (Or.inr (Or.inl ⟨rfl, hl4⟩))⟩).elim

private lemma twD_of_tag_twD {p l n : ℕ} (hΛ : LargeEvenInLambda2 ⟨.twD, l, n⟩)
    (hS : LargeEvenSplit p ⟨.twD, l, n⟩) (hVac : ¬ GGL48TableBVacLabel p ⟨.twD, l, n⟩)
    (hU4 : ¬ GGL48TBUFourRow p ⟨.twD, l, n⟩)
    (hO : ¬ GGTableBOrthSplitLabel p ⟨.twD, l, n⟩) : 4 ≤ l ∧ p ∣ 2 ^ n + 1 := by
  simp only [GGL48TableBVacLabel, GGCorFourTwoSmallLabel,
    TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel, GGStdSubSmallVacLabel,
    GGTableBTwDThreeLabel, GGB2derThreeLabel, StdSubRestThree.GGTwoThreeSmallLabel,
    GGLinearTwoLabel] at hVac
  simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hΛ hS
  simp at hS hVac
  obtain ⟨-, hl2⟩ := hΛ
  have hvne2 := hVac.2
  rcases hS with hq2 | hq1 | ⟨hn1, hp3⟩
  · by_cases hl : l = 2
    · exact (hvne2 hl).elim
    · by_cases hl3 : l = 3
      · exact (hU4 ⟨Or.inr rfl, hl3, hq2⟩).elim
      · exact ⟨by omega, hq2⟩
  · by_cases hl : l = 2
    · exact (hvne2 hl).elim
    · by_cases hl3 : l = 3
      · exact (hVac.1 hl3 hq1).elim
      · have hl4 : 4 ≤ l := by omega
        exact (hO ⟨Or.inr rfl, hl4, hq1⟩).elim
  · by_cases hl : l = 2
    · exact (hvne2 hl).elim
    · by_cases hl3 : l = 3
      · have hq2 : p ∣ 2 ^ n + 1 := by rw [hn1, hp3]; norm_num
        exact (hU4 ⟨Or.inr rfl, hl3, hq2⟩).elim
      · have hq2 : p ∣ 2 ^ n + 1 := by rw [hn1, hp3]; norm_num
        exact ⟨by omega, hq2⟩

private lemma false_of_tag_E6 {p l n : ℕ} (hS : LargeEvenSplit p ⟨.E6, l, n⟩)
    (hE2 : ¬ GGL48TBExcTwoRow p ⟨.E6, l, n⟩)
    (hE6 : ¬ GGL48TBE6Row p ⟨.E6, l, n⟩) : False := by
  simp only [LargeEvenUntwisted, LargeEvenSplit] at hS
  simp at hS
  rcases hS with hq1 | ⟨hn1, hp3⟩
  · exact (hE6 ⟨rfl, hq1⟩).elim
  · exact (hE2 ⟨Or.inl rfl, hn1, hp3⟩).elim

private lemma false_of_tag_E7 {p l n : ℕ} (hS : LargeEvenSplit p ⟨.E7, l, n⟩)
    (hEI : ¬ GGL48TBExcInnRow p ⟨.E7, l, n⟩)
    (hE2 : ¬ GGL48TBExcTwoRow p ⟨.E7, l, n⟩) : False := by
  simp only [LargeEvenUntwisted, LargeEvenSplit] at hS
  simp at hS
  rcases hS with hq1 | ⟨hn1, hp3⟩
  · exact (hEI ⟨Or.inl rfl, hq1⟩).elim
  · exact (hE2 ⟨Or.inr (Or.inl rfl), hn1, hp3⟩).elim

private lemma false_of_tag_E8 {p l n : ℕ} (hS : LargeEvenSplit p ⟨.E8, l, n⟩)
    (hEI : ¬ GGL48TBExcInnRow p ⟨.E8, l, n⟩)
    (hE2 : ¬ GGL48TBExcTwoRow p ⟨.E8, l, n⟩) : False := by
  simp only [LargeEvenUntwisted, LargeEvenSplit] at hS
  simp at hS
  rcases hS with hq1 | ⟨hn1, hp3⟩
  · exact (hEI ⟨Or.inr (Or.inl rfl), hq1⟩).elim
  · exact (hE2 ⟨Or.inr (Or.inr (Or.inl rfl)), hn1, hp3⟩).elim

private lemma false_of_tag_F4 {p l n : ℕ} (hS : LargeEvenSplit p ⟨.F4, l, n⟩)
    (hEI : ¬ GGL48TBExcInnRow p ⟨.F4, l, n⟩)
    (hE2 : ¬ GGL48TBExcTwoRow p ⟨.F4, l, n⟩) : False := by
  simp only [LargeEvenUntwisted, LargeEvenSplit] at hS
  simp at hS
  rcases hS with hq1 | ⟨hn1, hp3⟩
  · exact (hEI ⟨Or.inr (Or.inr rfl), hq1⟩).elim
  · exact (hE2 ⟨Or.inr (Or.inr (Or.inr rfl)), hn1, hp3⟩).elim

private lemma false_of_tag_twE6 {p l n : ℕ} (hp : p.Prime)
    (hΛ : LargeEvenInLambda2 ⟨.twE6, l, n⟩) (hS : LargeEvenSplit p ⟨.twE6, l, n⟩)
    (h0 : ¬ GGL48TB0TwRow p ⟨.twE6, l, n⟩)
    (htE6 : ¬ GGL48TBTwE6Row p ⟨.twE6, l, n⟩) : False := by
  simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hΛ hS
  simp at hS
  have hn : 1 ≤ n := hΛ.1
  have hq2 : p ∣ 2 ^ n + 1 := by
    rcases hS with h | ⟨hn1, hp3⟩
    · exact h
    · rw [hn1, hp3]; norm_num
  by_cases hp3 : p = 3
  · exact (h0 (Or.inr ⟨rfl, hp3, by simpa [hp3] using hq2⟩)).elim
  · have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hq2
    have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    exact (htE6 ⟨rfl, hp5, hq2⟩).elim

private lemma false_of_tag_triD4 {p l n : ℕ}
    (hVac : ¬ GGL48TableBVacLabel p ⟨.triD4, l, n⟩) : False := by
  exact hVac (by
    simp [GGL48TableBVacLabel, GGCorFourTwoSmallLabel,
      TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel])

private lemma false_of_tag_G2 {p l n : ℕ}
    (hVac : ¬ GGL48TableBVacLabel p ⟨.G2, l, n⟩) : False := by
  exact hVac (by
    simp [GGL48TableBVacLabel, GGCorFourTwoSmallLabel, GGStdSubSmallVacLabel])

private lemma false_of_tag_twB2 {p l n : ℕ}
    (hVac : ¬ GGL48TableBVacLabel p ⟨.twB2, l, n⟩) : False := by
  exact hVac (by
    simp [GGL48TableBVacLabel, GGCorFourTwoSmallLabel, GGStdSubSmallVacLabel])

private lemma false_of_tag_twF4 {p l n : ℕ}
    (hVac : ¬ GGL48TableBVacLabel p ⟨.twF4, l, n⟩) : False := by
  by_cases hp3 : p = 3
  · exact hVac (by simp [GGL48TableBVacLabel, hp3])
  · exact hVac (by
      simp [GGL48TableBVacLabel, GGCorFourTwoSmallLabel,
        TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel, hp3])

private lemma false_of_tag_B2der {p l n : ℕ} (hp : p.Prime)
    (hΛ : LargeEvenInLambda2 ⟨.B2der, l, n⟩) (hS : LargeEvenSplit p ⟨.B2der, l, n⟩)
    (hVac : ¬ GGL48TableBVacLabel p ⟨.B2der, l, n⟩) : False := by
  simp only [LargeEvenInLambda2, LargeEvenUntwisted, LargeEvenSplit] at hΛ hS
  simp at hS
  obtain ⟨-, -, hn1⟩ := hΛ
  rcases hS with hq1 | ⟨-, hp3⟩
  · exact (hp.not_dvd_one (by simpa [hn1] using hq1)).elim
  · subst hn1; subst hp3
    exact hVac (by
      simp [GGL48TableBVacLabel, GGCorFourTwoSmallLabel, GGStdSubSmallVacLabel,
        GGB2derThreeLabel])

private lemma false_of_tag_G2der {p l n : ℕ}
    (hVac : ¬ GGL48TableBVacLabel p ⟨.G2der, l, n⟩) : False := by
  exact hVac (by
    simp [GGL48TableBVacLabel, GGCorFourTwoSmallLabel,
      TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel])

private lemma false_of_tag_twF4der {p l n : ℕ}
    (hVac : ¬ GGL48TableBVacLabel p ⟨.twF4der, l, n⟩) : False := by
  exact hVac (by simp [GGL48TableBVacLabel, GGCorFourTwoSmallLabel])

theorem twD_of_rest22 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hΛ : LargeEvenInLambda2 lab) (hS : LargeEvenSplit p lab)
    (hVac : ¬ GGL48TableBVacLabel p lab) (h0 : ¬ GGL48TB0TwRow p lab)
    (hA : ¬ GGL48TBTypeARow p lab) (h2A : ¬ GGL48TBTwoARow p lab)
    (htA : ¬ GGL48TBTwistedARow p lab) (hEI : ¬ GGL48TBExcInnRow p lab)
    (hE2 : ¬ GGL48TBExcTwoRow p lab) (hE6 : ¬ GGL48TBE6Row p lab)
    (htE6 : ¬ GGL48TBTwE6Row p lab) (hD3 : ¬ GGL48TBDThreeRow p lab)
    (hIn : ¬ GGL48TBForm1InnerRow p lab) (hSp : ¬ GGTableBSympLabel p lab)
    (hU4 : ¬ GGL48TBUFourRow p lab) (hO : ¬ GGTableBOrthSplitLabel p lab) :
    lab.tag = .twD ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  · exact (false_of_tag_A hΛ hS hVac hA h2A).elim
  · exact (false_of_tag_twA hΛ hS hVac h0 htA hU4).elim
  · exact (false_of_tag_B hp hS hIn hSp).elim
  · exact (false_of_tag_C hp hS hIn hSp).elim
  · exact (false_of_tag_D hΛ hS hVac hD3 hIn hO).elim
  · exact ⟨rfl, twD_of_tag_twD hΛ hS hVac hU4 hO⟩
  · exact (false_of_tag_E6 hS hE2 hE6).elim
  · exact (false_of_tag_E7 hS hEI hE2).elim
  · exact (false_of_tag_E8 hS hEI hE2).elim
  · exact (false_of_tag_F4 hS hEI hE2).elim
  · exact (false_of_tag_twE6 hp hΛ hS h0 htE6).elim
  · exact (false_of_tag_triD4 hVac).elim
  · exact (false_of_tag_G2 hVac).elim
  · exact (false_of_tag_twB2 hVac).elim
  · exact (false_of_tag_twF4 hVac).elim
  · exact (false_of_tag_B2der hp hΛ hS hVac).elim
  · exact (false_of_tag_G2der hVac).elim
  · exact (false_of_tag_twF4der hVac).elim

theorem ggL48TBForm1Rest22_of_twD
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → lab.tag = .twD → 4 ≤ lab.rank →
      p ∣ 2 ^ lab.n + 1 → LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I) :
    GGL48TBForm1Rest22 := by
  intro p lab hp hΛ hS hVac hD4 h0 hA h2A htA hEI hE2 hE6 htE6 hD3 hIn hSp hU4 hO
  obtain ⟨ht, hr, hd⟩ :=
    twD_of_rest22 hp hΛ hS hVac h0 hA h2A htA hEI hE2 hE6 htE6 hD3 hIn hSp hU4 hO
  exact h p lab hp ht hr hd

theorem ggL48TBForm1Rest22_holds : GGL48TBForm1Rest22 :=
  ggL48TBForm1Rest22_of_twD fun _ _ hp ht h4 hpn =>
    CoverPOmMinusF.largeEvenLabelAll_coverP_omegaMinus_of_dvd_two_pow_add_one hp ht h4 hpn

end CFSG.StandardType
