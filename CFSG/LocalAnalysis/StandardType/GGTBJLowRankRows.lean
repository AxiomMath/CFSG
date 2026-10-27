module

public import CFSG.LocalAnalysis.StandardType.GGTBJLabelSides

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTBJLowRankOrdinaryLabel_iff {p : ℕ} {lab : LargeEvenLabel} :
    ggTBJLowRankOrdinaryLabel p lab ↔
      (lab.tag = .A ∧ (lab.rank = 1 ∨ lab.rank = 2)) ∨
        ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2) ∨
        (lab.tag = .twA ∧ lab.rank = 2) ∨ (lab.tag = .twD ∧ lab.rank = 2) := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp [ggTBJLowRankOrdinaryLabel, GGRootGenSmallRankLabel, ggTBJExoticTag]

theorem GGResHyp.not_lowRankOrdinary
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hMark : GGInnerDiagOnLabel ggTBJLowRankOrdinaryLabel p Bs X) : False := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hSmall : GGInnerDiagOnLabel GGRootGenSmallRankLabel p Bs X :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.1, hP.2⟩) hMark
  apply not_largeEvenMarking_smallRank (X := ↥X) Fact.out hp2
  rcases hX with rfl | rfl
  · exact ggInnerDiagOnLabel_L_pRank_ge_three hH.1 hSmall
  · exact ggInnerDiagOnLabel_nbr_pRank_ge_three hH.1 hH.2.2.2.2.1 hSmall

theorem ggTBJLowRankOrdinaryLeft : GGTBJLeftOn ggTBJLowRankOrdinaryLabel := by
  intro G _ _ p B Bs x L D J y K hH _ hMark _
  exact (hH.not_lowRankOrdinary (Or.inl rfl) hMark).elim

theorem ggTBJLowRankOrdinaryNbr : GGTBJNbrOn ggTBJLowRankOrdinaryLabel := by
  intro G _ _ p B Bs x L D J y K hH _ hMark _
  exact (hH.not_lowRankOrdinary (Or.inr rfl) hMark).elim

theorem ggTBJOrdinaryInput_of_rest (h : GGTBJOrdinaryRestInput) : GGTBJOrdinaryInput := by
  classical
  constructor
  · refine (h.1.or ggTBJLowRankOrdinaryLeft).mono fun p lab hOrd => ?_
    by_cases hSmall : GGRootGenSmallRankLabel p lab
    · exact Or.inr ⟨hSmall, hOrd⟩
    · exact Or.inl ⟨hOrd, hSmall⟩
  · refine (h.2.or ggTBJLowRankOrdinaryNbr).mono fun p lab hOrd => ?_
    by_cases hSmall : GGRootGenSmallRankLabel p lab
    · exact Or.inr ⟨hSmall, hOrd⟩
    · exact Or.inl ⟨hOrd, hSmall⟩

theorem GGResHyp.not_fieldTwo
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hMark : GGInnerDiagOnLabel ggTBJFieldTwoLabel p Bs X) : False := by
  have hSmall : GGInnerDiagOnLabel StdSubRestThree.GGTwoThreeSmallLabel p Bs X :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.1, hP.2⟩) hMark
  have hBound := not_largeEvenMarking_of_labelAll_card_lt (X := ↥X)
    (S := fun lab => StdSubRestThree.GGTwoThreeSmallLabel p lab)
    (fun _ _ h => (StdSubRestThree.largeEvenLabelAll_card_lt_twoThreeSmall h).mono
      fun _ _ _ _ h' _ _ => h')
  apply hBound
  rcases hX with rfl | rfl
  · exact ggInnerDiagOnLabel_L_pRank_ge_three hH.1 hSmall
  · exact ggInnerDiagOnLabel_nbr_pRank_ge_three hH.1 hH.2.2.2.2.1 hSmall

theorem ggTBJFieldTwoLeft : GGTBJLeftOn ggTBJFieldTwoLabel := by
  intro G _ _ p B Bs x L D J y K hH _ hMark _
  exact (hH.not_fieldTwo (Or.inl rfl) hMark).elim

theorem ggTBJFieldTwoNbr : GGTBJNbrOn ggTBJFieldTwoLabel := by
  intro G _ _ p B Bs x L D J y K hH _ hMark _
  exact (hH.not_fieldTwo (Or.inr rfl) hMark).elim

theorem ggTBJOrdinaryRestInput_of_fieldTwo (h : GGTBJFieldTwoRestInput) :
    GGTBJOrdinaryRestInput := by
  classical
  constructor
  · refine (h.1.or ggTBJFieldTwoLeft).mono fun p lab hOrd => ?_
    by_cases hTwo : ggTBJFieldTwoLabel p lab
    · exact Or.inr hTwo
    · exact Or.inl ⟨hOrd, hTwo⟩
  · refine (h.2.or ggTBJFieldTwoNbr).mono fun p lab hOrd => ?_
    by_cases hTwo : ggTBJFieldTwoLabel p lab
    · exact Or.inr hTwo
    · exact Or.inl ⟨hOrd, hTwo⟩

end CFSG.StandardType

end
