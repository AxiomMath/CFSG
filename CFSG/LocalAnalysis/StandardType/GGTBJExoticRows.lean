module

public import CFSG.LocalAnalysis.StandardType.GGTBJLabelSides
public import CFSG.LocalAnalysis.StandardType.GGResE6DepSmall
public import CFSG.LocalAnalysis.StandardType.GGTBWNormSmall
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Absence
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem largeEvenLabelAll_card_lt_exotic_of_ne_twF4 {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hTag : ggTBJExoticTag p lab) (hRee : lab.tag ≠ .twF4) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
      (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E → Nat.card E < p ^ 3 := by
  unfold ggTBJExoticTag at hTag
  rcases hTag with ht | ht | ht | ht | ht | ht | ht
  · exact NbrInnerNine.largeEvenLabelAll_card_lt_triD4_all hp hp2 hΛ ht
  · exact NbrInnerNine.largeEvenLabelAll_card_lt_G2_all hp hp2 ht
  · exact NbrInnerNine.largeEvenLabelAll_card_lt_twB2_all hp hp2 hΛ ht
  · exact (hRee ht).elim
  · by_cases hp3 : p = 3
    · subst p
      exact ggCSR_B2der hΛ ht
    · exact NbrInnerNine.largeEvenLabelAll_card_lt_b2der_ne_three hp hp2 hp3 ht
  · by_cases hp3 : p = 3
    · subst p
      exact ggCSR_G2der hΛ ht
    · exact NbrInnerNine.largeEvenLabelAll_card_lt_G2der_ne_three hp hp2 hp3 ht
  · by_cases hp3 : p = 3
    · subst p
      exact ggCSR_twF4der hΛ ht
    · exact NbrInnerNine.largeEvenLabelAll_card_lt_twF4der_ne_three hp hp2 hp3 hΛ ht

theorem GGResHyp.not_exotic_of_ne_twF4
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hMark : GGInnerDiagOnLabel
      (fun p lab => ggTBJExoticTag p lab ∧ lab.tag ≠ .twF4) p Bs X) : False := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  refine hH.not_innerDiagOnLabel_of_card_lt hX ?_ hMark
  intro lab hΛ hTag
  exact largeEvenLabelAll_card_lt_exotic_of_ne_twF4 Fact.out hp2 hΛ hTag.1 hTag.2

theorem ggTBJLeftOn_exotic_of_ne_twF4 :
    GGTBJLeftOn fun p lab => ggTBJExoticTag p lab ∧ lab.tag ≠ .twF4 := by
  intro G _ _ p B Bs x L D J y K hH _ hMark _
  exact (hH.not_exotic_of_ne_twF4 (Or.inl rfl) hMark).elim

theorem ggTBJNbrOn_exotic_of_ne_twF4 :
    GGTBJNbrOn fun p lab => ggTBJExoticTag p lab ∧ lab.tag ≠ .twF4 := by
  intro G _ _ p B Bs x L D J y K hH _ hMark _
  exact (hH.not_exotic_of_ne_twF4 (Or.inr rfl) hMark).elim

theorem ggTBJLeftOn_twF4 : GGTBJLeftOn fun _ lab => lab.tag = .twF4 := by
  intro G _ _ p B Bs x L D J y K hH _ hMark _
  exfalso
  refine ggConfig_false_of_rigid_label (S := fun _ lab => lab.tag = .twF4)
    ggLabelRigidInput_holds ?_ ?_ hH.1
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) hMark)
  · intro p lab lab' ht hIso
    exact ggLabelIso_eq_of_exceptional (by rw [ht]; decide) (by rw [ht]; decide)
      (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide)
      (by rw [ht]; decide) hIso
  · intro p lab hp hΛ ht hSplit
    exact TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4
      (TableBExcSmallRanks.ggTwF4RankInput_of_three TwF4SUThree.ggTwF4ThreeRankInput_holds)
      hp hΛ ht hSplit

theorem ggTBJExoticLeft : GGTBJLeftOn ggTBJExoticTag := by
  have h := ggTBJLeftOn_exotic_of_ne_twF4.or ggTBJLeftOn_twF4
  refine h.mono fun p lab hTag => ?_
  by_cases ht : lab.tag = .twF4
  · exact Or.inr ht
  · exact Or.inl ⟨hTag, ht⟩

theorem ggTBJNbrOn_twF4 : GGTBJNbrOn fun _ lab => lab.tag = .twF4 := by
  intro G _ _ p B Bs x L D J y K hH _ hMark _
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  exfalso
  refine hH.not_innerDiagOnLabel_of_card_lt (Or.inr rfl) ?_ hMark
  intro lab hΛ ht
  exact NbrInnerNine.largeEvenLabelAll_card_lt_twF4_all Fact.out hp2 hΛ ht

theorem ggTBJExoticNbr : GGTBJNbrOn ggTBJExoticTag := by
  have h := ggTBJNbrOn_exotic_of_ne_twF4.or ggTBJNbrOn_twF4
  refine h.mono fun p lab hTag => ?_
  by_cases ht : lab.tag = .twF4
  · exact Or.inr ht
  · exact Or.inl ⟨hTag, ht⟩

theorem ggTBJInputR_of_ordinary (h : GGTBJOrdinaryInput) : GGTBJInputR := by
  classical
  apply ggTBJInputR_of_labels
  · refine (h.1.or ggTBJExoticLeft).mono fun p lab _ => ?_
    exact (em (ggTBJExoticTag p lab)).symm
  · refine (h.2.or ggTBJExoticNbr).mono fun p lab _ => ?_
    exact (em (ggTBJExoticTag p lab)).symm

end CFSG.StandardType

end
