module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoRestTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanks
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallTits
public import CFSG.LocalAnalysis.StandardType.GGTableBTwDThree
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestVac

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Small

variable {S : ℕ → LargeEvenLabel → Prop}

theorem ggCorFourTwoInputsOn_of_small
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3) :
    GGBstarInnerDiagLInputOn S ∧ GGLTransvectionCenterInputOn S ∧
      GGLNoInvariantLineInputOn S ∧ GGTableBCxInputOn S ∧ GGTableBModuleInputOn S ∧
        GGTableBActionInputOn S := by
  have hBs : ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
      {L D J : Subgroup G}, GGConfig p B Bs x L D J → GGInnerDiagOnLab S p Bs L → False := by
    intro G _ _ p B Bs x L D J hC hL
    exact ggThmIHyp_false_of_labelAll h hC.1 (largeEvenMarking_mono
      (fun _ _ _ _ _ _ hP => ⟨hP.1, hP.2.1, hC.2.1.1.trans hP.2.2.1,
        fun b hb => hP.2.2.2 b (hC.2.1.1 hb)⟩) hL)
  refine ⟨fun G _ _ p B Bs x L D J hC hL => (ggThmIHyp_false_of_labelAll h hC.1 hL).elim,
    fun G _ _ p B Bs x L D J hC hL => (hBs hC hL).elim,
    fun G _ _ p B Bs x L D J hC hL => (hBs hC hL).elim,
    fun G _ _ p B Bs x L D J hC hL => (ggThmIHyp_false_of_labelAll h hC.1 hL).elim,
    fun G _ _ p B Bs x L D J hC hL => (ggThmIHyp_false_of_labelAll h hC.1 hL).elim,
    fun G _ _ p B Bs x L D J B₂ hC hL => (ggThmIHyp_false_of_labelAll h hC.1 hL).elim⟩

end Small

@[expose] def GGCorFourTwoSmallLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel p lab ∨ lab.tag = .twF4der ∨
    GGStdSubSmallVacLabel p lab

theorem GGCorFourTwoSmallLabel.tag {p : ℕ} {lab : LargeEvenLabel}
    (h : GGCorFourTwoSmallLabel p lab) :
    (lab.tag = .G2der ∨ lab.tag = .triD4 ∨ lab.tag = .twF4 ∨ lab.tag = .twF4der ∨
      lab.tag = .B2der ∨ lab.tag = .G2 ∨ lab.tag = .twB2) ∨ (lab.tag = .twD ∧ lab.rank = 3) := by
  rcases h with (h | h | ⟨h, -⟩) | h | (h | h | ⟨h, h', -⟩ | ⟨-, h⟩)
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  · exact Or.inr ⟨h, h'⟩
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

section Certs


theorem largeEvenLabelAll_card_lt_corFourTwoSmall {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hlab : LargeEvenInLambda2 lab) (h : GGCorFourTwoSmallLabel p lab)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  rcases h with h | h | h | h | h | h
  · exact TableBExcSmallRanks.largeEvenLabelAll_card_lt_smallRanksDone hp hlab h hs
  · exact TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der_holds hp hlab h hs
  · exact TableBExc.largeEvenLabelAll_card_lt_G2TwB2 hp hlab (Or.inl h) hs
  · exact TableBExc.largeEvenLabelAll_card_lt_G2TwB2 hp hlab (Or.inr h) hs
  · exact largeEvenLabelAll_card_lt_twDThree hp hlab h
  · exact largeEvenLabelAll_card_lt_b2derThree h

theorem ggCorFourTwoInputsOn_small :
    GGBstarInnerDiagLInputOn GGCorFourTwoSmallLabel ∧
      GGLTransvectionCenterInputOn GGCorFourTwoSmallLabel ∧
      GGLNoInvariantLineInputOn GGCorFourTwoSmallLabel ∧
      GGTableBCxInputOn GGCorFourTwoSmallLabel ∧ GGTableBModuleInputOn GGCorFourTwoSmallLabel ∧
        GGTableBActionInputOn GGCorFourTwoSmallLabel :=
  ggCorFourTwoInputsOn_of_small fun _ _ hp hlab h hs =>
    largeEvenLabelAll_card_lt_corFourTwoSmall hp hlab h hs

end Certs

@[expose] def GGCorFourTwoOpenLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoRestSpLabel p lab ∧ ¬ GGCorFourTwoSmallLabel p lab

@[expose] def GGCorFourTwoOpenLIDLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoRestLIDLabel p lab ∧ ¬ GGCorFourTwoSmallLabel p lab

theorem ggCorFourTwoRestSpLabel_cover (p : ℕ) (lab : LargeEvenLabel)
    (h : GGCorFourTwoRestSpLabel p lab) (_ : LargeEvenSplit p lab) :
    GGCorFourTwoSmallLabel p lab ∨ GGCorFourTwoOpenLabel p lab := by
  by_cases h1 : GGCorFourTwoSmallLabel p lab
  · exact Or.inl h1
  · exact Or.inr ⟨h, h1⟩

theorem GGCorFourTwoSmallLabel.restLID {p : ℕ} {lab : LargeEvenLabel}
    (h : GGCorFourTwoSmallLabel p lab) (hs : LargeEvenSplit p lab) :
    GGCorFourTwoRestLIDLabel p lab := by
  have ht := h.tag
  refine ⟨⟨?_, ?_, hs⟩, ?_, ?_⟩
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, h1', -⟩)
    · rcases ht with (h2 | h2 | h2 | h2 | h2 | h2 | h2) | ⟨h2, -⟩ <;> rw [h2] at h1 <;>
        exact absurd h1 (by decide)
    · rcases ht with (h2 | h2 | h2 | h2 | h2 | h2 | h2) | ⟨h2, -⟩ <;> rw [h2] at h1 <;>
        exact absurd h1 (by decide)
    · rcases ht with (h2 | h2 | h2 | h2 | h2 | h2 | h2) | ⟨-, h2⟩
      all_goals first
        | (rw [h2] at h1; exact absurd h1 (by decide))
        | omega
  · rintro ⟨h1 | h1, -⟩ <;>
      rcases ht with (h2 | h2 | h2 | h2 | h2 | h2 | h2) | ⟨h2, -⟩ <;> rw [h2] at h1 <;>
        exact absurd h1 (by decide)
  · rintro ⟨-, -, h1 | ⟨h1, -⟩⟩ <;>
      rcases ht with (h2 | h2 | h2 | h2 | h2 | h2 | h2) | ⟨h2, -⟩ <;> rw [h2] at h1 <;>
        exact absurd h1 (by decide)
  · rintro ⟨-, -, h1 | h1⟩ <;>
      rcases ht with (h2 | h2 | h2 | h2 | h2 | h2 | h2) | ⟨h2, -⟩ <;> rw [h2] at h1 <;>
        exact absurd h1 (by decide)

section Certs


theorem ggBstarInnerDiagLInputOn_restLID_of_open
    (h : GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDLabel) :
    GGBstarInnerDiagLInputOn GGCorFourTwoRestLIDLabel := by
  have h' := ggCorFourTwoInputsOn_small.1.or h
  intro G _ _ p B Bs x L D J hC hL
  refine (h' G p B Bs x L D J hC (hL.mono_split fun p lab hlab _ => ?_)).mono_split
    fun p lab hlab hs => ?_
  · by_cases h1 : GGCorFourTwoSmallLabel p lab
    · exact Or.inl h1
    · exact Or.inr ⟨hlab, h1⟩
  · rcases hlab with h1 | h1
    · exact h1.restLID hs
    · exact h1.1

theorem ggLTransvectionCenterInputOn_restSp_of_open
    (h : GGLTransvectionCenterInputOn GGCorFourTwoOpenLabel) :
    GGLTransvectionCenterInputOn GGCorFourTwoRestSpLabel := by
  have h' := ggCorFourTwoInputsOn_small.2.1.or h
  intro G _ _ p B Bs x L D J hC hL
  exact h' G p B Bs x L D J hC (hL.mono_split ggCorFourTwoRestSpLabel_cover)

theorem ggLNoInvariantLineInputOn_restSp_of_open
    (h : GGLNoInvariantLineInputOn GGCorFourTwoOpenLabel) :
    GGLNoInvariantLineInputOn GGCorFourTwoRestSpLabel := by
  have h' := ggCorFourTwoInputsOn_small.2.2.1.or h
  intro G _ _ p B Bs x L D J hC hL
  exact h' G p B Bs x L D J hC (hL.mono_split ggCorFourTwoRestSpLabel_cover)

theorem ggTableBCxInputOn_restSp_of_open (h : GGTableBCxInputOn GGCorFourTwoOpenLabel) :
    GGTableBCxInputOn GGCorFourTwoRestSpLabel := by
  have h' := ggCorFourTwoInputsOn_small.2.2.2.1.or h
  intro G _ _ p B Bs x L D J hC hL
  exact h' G p B Bs x L D J hC (hL.mono_split ggCorFourTwoRestSpLabel_cover)

theorem ggTableBModuleInputOn_restSp_of_open (h : GGTableBModuleInputOn GGCorFourTwoOpenLabel) :
    GGTableBModuleInputOn GGCorFourTwoRestSpLabel := by
  have h' := ggCorFourTwoInputsOn_small.2.2.2.2.1.or h
  intro G _ _ p B Bs x L D J hC hL
  exact h' G p B Bs x L D J hC (hL.mono_split ggCorFourTwoRestSpLabel_cover)

theorem ggTableBActionInputOn_restSp_of_open (h : GGTableBActionInputOn GGCorFourTwoOpenLabel) :
    GGTableBActionInputOn GGCorFourTwoRestSpLabel := by
  have h' := ggCorFourTwoInputsOn_small.2.2.2.2.2.or h
  intro G _ _ p B Bs x L D J B₂ hC hL
  exact h' G p B Bs x L D J B₂ hC (hL.mono_split ggCorFourTwoRestSpLabel_cover)

theorem ggCor42Input_of_open (hK : GGKantorReductionInput)
    (hLID : GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDLabel)
    (hcen : GGLTransvectionCenterInputOn GGCorFourTwoOpenLabel)
    (hline : GGLNoInvariantLineInputOn GGCorFourTwoOpenLabel)
    (hnorm : GGBstarNbrNormalInput) (hgraph : GGNbrGraphInput)
    (hfield : GGNbrFieldTransvectionInput) : GGCor42Input :=
  ggCor42Input_of_restLID hK (ggBstarInnerDiagLInputOn_restLID_of_open hLID)
    (ggLTransvectionCenterInputOn_restSp_of_open hcen)
    (ggLNoInvariantLineInputOn_restSp_of_open hline) hnorm hgraph hfield

theorem ggNoTransvectionInput_of_open (hK : GGKantorReductionInput)
    (hLID : GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDLabel)
    (hcen : GGLTransvectionCenterInputOn GGCorFourTwoOpenLabel)
    (hline : GGLNoInvariantLineInputOn GGCorFourTwoOpenLabel) : GGNoTransvectionInput :=
  ggNoTransvectionInput_of_restLID hK (ggBstarInnerDiagLInputOn_restLID_of_open hLID)
    (ggLTransvectionCenterInputOn_restSp_of_open hcen)
    (ggLNoInvariantLineInputOn_restSp_of_open hline)

theorem ggTableBCxInput_of_open (h : GGTableBCxInputOn GGCorFourTwoOpenLabel) :
    GGTableBCxInput :=
  ggTableBCxInput_of_restSp (ggTableBCxInputOn_restSp_of_open h)

theorem ggTableBModuleInput_of_open (h : GGTableBModuleInputOn GGCorFourTwoOpenLabel) :
    GGTableBModuleInput :=
  ggTableBModuleInput_of_restSp (ggTableBModuleInputOn_restSp_of_open h)

theorem ggTableBActionInput_of_open (h : GGTableBActionInputOn GGCorFourTwoOpenLabel) :
    GGTableBActionInput :=
  ggTableBActionInput_of_restSp (ggTableBActionInputOn_restSp_of_open h)

end Certs

end CFSG.StandardType

end
