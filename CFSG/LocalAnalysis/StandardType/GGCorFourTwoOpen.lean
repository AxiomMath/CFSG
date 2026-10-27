module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenVac
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenUnitaryIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGCorFourTwoOpenLIDRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenLIDLabel p lab ∧ ¬ GGCorFourTwoOrthSplitLabel p lab ∧
    ¬ GGCorFourTwoOpenVacLabel p lab

@[expose] def GGCorFourTwoOpenLineRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenLabel p lab ∧ ¬ GGCorFourTwoOrthSplitLabel p lab ∧
    ¬ GGUnitaryCoprimeLabel p lab

theorem ggBstarInnerDiagLInputOn_openLID_of_rest (ha₀ : GGLNoncyclicInput)
    (h : GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRestLabel) :
    GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDLabel := by
  have h' := ((ggBstarInnerDiagLInputOn_orthSplit GGCorFourTwoOpenLIDLabel).or
    (ggBstarInnerDiagLInputOn_vac ha₀ GGCorFourTwoOpenLIDLabel)).or h
  intro G _ _ p B Bs x L D J hC hL
  refine (h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)).mono fun p lab hlab => ?_
  · by_cases h1 : GGCorFourTwoOrthSplitLabel p lab
    · exact Or.inl (Or.inl ⟨hlab, h1⟩)
    · by_cases h2 : GGCorFourTwoOpenVacLabel p lab
      · exact Or.inl (Or.inr ⟨hlab, h2⟩)
      · exact Or.inr ⟨hlab, h1, h2⟩
  · rcases hlab with (h1 | h1) | h1
    · exact h1.1
    · exact h1.1
    · exact h1.1

theorem ggLNoInvariantLineInputOn_open_of_rest
    (h : GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRestLabel) :
    GGLNoInvariantLineInputOn GGCorFourTwoOpenLabel := by
  have h' := (ggLNoInvariantLineInputOn_orthSplit.or ggLNoInvariantLineInputOn_unitary).or h
  intro G _ _ p B Bs x L D J hC hL
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)
  by_cases h1 : GGCorFourTwoOrthSplitLabel p lab
  · exact Or.inl (Or.inl h1)
  · by_cases h2 : GGUnitaryCoprimeLabel p lab
    · exact Or.inl (Or.inr h2)
    · exact Or.inr ⟨hlab, h1, h2⟩

@[expose] def GGCorFourTwoOpenTableBRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenLabel p lab ∧ ¬ (GGUnitaryCoprimeLabel p lab ∧ GGCorFourTwoOpenVacLabel p lab)

section TableB


theorem ggTableBCxInputOn_open_of_rest (ha₀ : GGLNoncyclicInput)
    (h : GGTableBCxInputOn GGCorFourTwoOpenTableBRestLabel) :
    GGTableBCxInputOn GGCorFourTwoOpenLabel := by
  have h' := (ggTableBCxInputOn_unitaryVac ha₀).or h
  intro G _ _ p B Bs x L D J hC hL
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)
  by_cases h1 : GGUnitaryCoprimeLabel p lab ∧ GGCorFourTwoOpenVacLabel p lab
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩

theorem ggTableBModuleInputOn_open_of_rest (ha₀ : GGLNoncyclicInput)
    (h : GGTableBModuleInputOn GGCorFourTwoOpenTableBRestLabel) :
    GGTableBModuleInputOn GGCorFourTwoOpenLabel := by
  have h' := (ggTableBModuleInputOn_unitaryVac ha₀).or h
  intro G _ _ p B Bs x L D J hC hL
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)
  by_cases h1 : GGUnitaryCoprimeLabel p lab ∧ GGCorFourTwoOpenVacLabel p lab
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩

theorem ggTableBActionInputOn_open_of_rest (ha₀ : GGLNoncyclicInput)
    (h : GGTableBActionInputOn GGCorFourTwoOpenTableBRestLabel) :
    GGTableBActionInputOn GGCorFourTwoOpenLabel := by
  have h' := (ggTableBActionInputOn_unitaryVac ha₀).or h
  intro G _ _ p B Bs x L D J B₂ hC hL
  refine h' G p B Bs x L D J B₂ hC (hL.mono fun p lab hlab => ?_)
  by_cases h1 : GGUnitaryCoprimeLabel p lab ∧ GGCorFourTwoOpenVacLabel p lab
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩

end TableB

section Certs


theorem ggCor42Input_of_openRest (hK : GGKantorReductionInput)
    (hLID : GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRestLabel)
    (hcen : GGLTransvectionCenterInputOn GGCorFourTwoOpenLabel)
    (hline : GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRestLabel)
    (hnorm : GGBstarNbrNormalInput) (hgraph : GGNbrGraphInput)
    (hfield : GGNbrFieldTransvectionInput) : GGCor42Input :=
  ggCor42Input_of_open hK (ggBstarInnerDiagLInputOn_openLID_of_rest ggLNoncyclicInput_holds hLID)
    hcen (ggLNoInvariantLineInputOn_open_of_rest hline) hnorm hgraph hfield

theorem ggNoTransvectionInput_of_openRest (hK : GGKantorReductionInput)
    (hLID : GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRestLabel)
    (hcen : GGLTransvectionCenterInputOn GGCorFourTwoOpenLabel)
    (hline : GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRestLabel) : GGNoTransvectionInput :=
  ggNoTransvectionInput_of_open hK
    (ggBstarInnerDiagLInputOn_openLID_of_rest ggLNoncyclicInput_holds hLID) hcen
    (ggLNoInvariantLineInputOn_open_of_rest hline)

theorem ggTableBCxInput_of_openRest (h : GGTableBCxInputOn GGCorFourTwoOpenTableBRestLabel) :
    GGTableBCxInput :=
  ggTableBCxInput_of_open (ggTableBCxInputOn_open_of_rest ggLNoncyclicInput_holds h)

theorem ggTableBModuleInput_of_openRest
    (h : GGTableBModuleInputOn GGCorFourTwoOpenTableBRestLabel) : GGTableBModuleInput :=
  ggTableBModuleInput_of_open (ggTableBModuleInputOn_open_of_rest ggLNoncyclicInput_holds h)

theorem ggTableBActionInput_of_openRest
    (h : GGTableBActionInputOn GGCorFourTwoOpenTableBRestLabel) : GGTableBActionInput :=
  ggTableBActionInput_of_open (ggTableBActionInputOn_open_of_rest ggLNoncyclicInput_holds h)

end Certs

end CFSG.StandardType

end
