module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoRestSp
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGCorFourTwoRestSpLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoRestLabel p lab ∧ ¬ GGReflSpLabel p lab ∧ LargeEvenSplit p lab

theorem GGReflSpLabel.corFourTwoRest {p : ℕ} {lab : LargeEvenLabel} (h : GGReflSpLabel p lab) :
    GGCorFourTwoRestLabel p lab := by
  rintro (⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩) <;> rcases h.1 with h1 | h1 <;> rw [h1] at h' <;>
    exact absurd h' (by decide)

theorem ggCorFourTwoRestLabel_cover (p : ℕ) (lab : LargeEvenLabel)
    (h : GGCorFourTwoRestLabel p lab) (hs : LargeEvenSplit p lab) :
    GGReflSpLabel p lab ∨ GGCorFourTwoRestSpLabel p lab := by
  by_cases hsp : GGReflSpLabel p lab
  · exact Or.inl hsp
  · exact Or.inr ⟨h, hsp, hs⟩

theorem ggCorFourTwoRestLabel_of_cover (p : ℕ) (lab : LargeEvenLabel)
    (h : GGReflSpLabel p lab ∨ GGCorFourTwoRestSpLabel p lab) : GGCorFourTwoRestLabel p lab :=
  h.elim GGReflSpLabel.corFourTwoRest fun h => h.1

section Lab

variable {G : Type} [Group G] {S T : ℕ → LargeEvenLabel → Prop} {p : ℕ} {Bs L : Subgroup G}

theorem GGInnerDiagOnLab.mono_split (hST : ∀ p lab, S p lab → LargeEvenSplit p lab → T p lab)
    (h : GGInnerDiagOnLab S p Bs L) : GGInnerDiagOnLab T p Bs L :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hST _ _ hP.1 hP.2.1, hP.2⟩) h

end Lab

theorem ggBstarInnerDiagLInputOn_rest_of_restSp
    (h : GGBstarInnerDiagLInputOn GGCorFourTwoRestSpLabel) :
    GGBstarInnerDiagLInputOn GGCorFourTwoRestLabel := by
  have h' := ggBstarInnerDiagLInputOn_symplectic.or h
  intro G _ _ p B Bs x L D J hC hL
  exact (h' G p B Bs x L D J hC (hL.mono_split ggCorFourTwoRestLabel_cover)).mono
    ggCorFourTwoRestLabel_of_cover

theorem ggLTransvectionCenterInputOn_rest_of_restSp
    (h : GGLTransvectionCenterInputOn GGCorFourTwoRestSpLabel) :
    GGLTransvectionCenterInputOn GGCorFourTwoRestLabel := by
  have h' := ggLTransvectionCenterInputOn_symplectic.or h
  intro G _ _ p B Bs x L D J hC hL
  exact h' G p B Bs x L D J hC (hL.mono_split ggCorFourTwoRestLabel_cover)

theorem ggLNoInvariantLineInputOn_rest_of_restSp
    (h : GGLNoInvariantLineInputOn GGCorFourTwoRestSpLabel) :
    GGLNoInvariantLineInputOn GGCorFourTwoRestLabel := by
  have h' := ggLNoInvariantLineInputOn_symplectic.or h
  intro G _ _ p B Bs x L D J hC hL
  exact h' G p B Bs x L D J hC (hL.mono_split ggCorFourTwoRestLabel_cover)

theorem ggTableBCxInputOn_rest_of_restSp (h : GGTableBCxInputOn GGCorFourTwoRestSpLabel) :
    GGTableBCxInputOn GGCorFourTwoRestLabel := by
  have h' := ggTableBCxInputOn_symplectic.or h
  intro G _ _ p B Bs x L D J hC hL
  exact h' G p B Bs x L D J hC (hL.mono_split ggCorFourTwoRestLabel_cover)

theorem ggTableBModuleInputOn_rest_of_restSp (h : GGTableBModuleInputOn GGCorFourTwoRestSpLabel) :
    GGTableBModuleInputOn GGCorFourTwoRestLabel := by
  have h' := ggTableBModuleInputOn_symplectic.or h
  intro G _ _ p B Bs x L D J hC hL
  exact h' G p B Bs x L D J hC (hL.mono_split ggCorFourTwoRestLabel_cover)

theorem ggTableBActionInputOn_rest_of_restSp (h : GGTableBActionInputOn GGCorFourTwoRestSpLabel) :
    GGTableBActionInputOn GGCorFourTwoRestLabel := by
  have h' := ggTableBActionInputOn_symplectic.or h
  intro G _ _ p B Bs x L D J B₂ hC hL
  exact h' G p B Bs x L D J B₂ hC (hL.mono_split ggCorFourTwoRestLabel_cover)

theorem ggCor42Input_of_restSp
    (hK : GGKantorReductionInput)
    (hLID : GGBstarInnerDiagLInputOn GGCorFourTwoRestSpLabel)
    (hcen : GGLTransvectionCenterInputOn GGCorFourTwoRestSpLabel)
    (hline : GGLNoInvariantLineInputOn GGCorFourTwoRestSpLabel)
    (hnorm : GGBstarNbrNormalInput) (hgraph : GGNbrGraphInput)
    (hfield : GGNbrFieldTransvectionInput) : GGCor42Input :=
  ggCor42Input_of_typeA hK (ggBstarInnerDiagLInputOn_rest_of_restSp hLID)
    (ggLTransvectionCenterInputOn_rest_of_restSp hcen)
    (ggLNoInvariantLineInputOn_rest_of_restSp hline) hnorm hgraph hfield

theorem ggNoTransvectionInput_of_restSp
    (hK : GGKantorReductionInput)
    (hLID : GGBstarInnerDiagLInputOn GGCorFourTwoRestSpLabel)
    (hcen : GGLTransvectionCenterInputOn GGCorFourTwoRestSpLabel)
    (hline : GGLNoInvariantLineInputOn GGCorFourTwoRestSpLabel) : GGNoTransvectionInput :=
  ggNoTransvectionInput_of_typeA hK (ggBstarInnerDiagLInputOn_rest_of_restSp hLID)
    (ggLTransvectionCenterInputOn_rest_of_restSp hcen)
    (ggLNoInvariantLineInputOn_rest_of_restSp hline)

theorem ggTableBCxInput_of_restSp (h : GGTableBCxInputOn GGCorFourTwoRestSpLabel) :
    GGTableBCxInput :=
  ggTableBCxInput_of_rest (ggTableBCxInputOn_rest_of_restSp h)

theorem ggTableBModuleInput_of_restSp (h : GGTableBModuleInputOn GGCorFourTwoRestSpLabel) :
    GGTableBModuleInput :=
  ggTableBModuleInput_of_rest (ggTableBModuleInputOn_rest_of_restSp h)

theorem ggTableBActionInput_of_restSp (h : GGTableBActionInputOn GGCorFourTwoRestSpLabel) :
    GGTableBActionInput :=
  ggTableBActionInput_of_rest (ggTableBActionInputOn_rest_of_restSp h)

end CFSG.StandardType

end
