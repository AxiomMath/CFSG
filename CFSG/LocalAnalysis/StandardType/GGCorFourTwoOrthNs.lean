module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMore
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNine

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGCorFourTwoOpenTableBRest2NsLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenTableBRest2Label p lab ∧ ¬ GGOrthNsVacLabel p lab

@[expose] def GGCorFourTwoOpenLineRestNsLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenLineRestLabel p lab ∧ ¬ GGOrthNsLabel p lab

@[expose] def GGTableBNbrInnerRound10NsLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBNbrInnerRound10Label p lab ∧ ¬ GGOrthNsLabel p lab

section FromLID


theorem ggTableBCxInputOn_of_orthNs {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGOrthNsLabel p lab) (hD : GGBstarInnerDiagLInputOn S) :
    GGTableBCxInputOn S :=
  ggTableBCxInputOn_of_irred hD (ggTableBIrredInputOn_orthNs.mono hS)

theorem ggTableBModuleInputOn_of_orthNs {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGOrthNsLabel p lab) (hD : GGBstarInnerDiagLInputOn S) :
    GGTableBModuleInputOn S :=
  ggTableBModuleInputOn_of_irred hD (ggTableBIrredInputOn_orthNs.mono hS)

theorem ggTableBActionInputOn_of_orthNs {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGOrthNsLabel p lab) (hD : GGBstarInnerDiagLInputOn S) :
    GGTableBActionInputOn S :=
  ggTableBActionInputOn_of_irred hD (ggTableBIrredInputOn_orthNs.mono hS)

theorem ggTableBNbrInnerInputOn_of_not_orthNs {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBNbrInnerInputOn fun p lab => S p lab ∧ ¬ GGOrthNsLabel p lab) :
    GGTableBNbrInnerInputOn S :=
  (ggTableBNbrInnerInputOn_orthNs.or h).mono fun p lab hS => by
    by_cases h' : GGOrthNsLabel p lab
    · exact Or.inl h'
    · exact Or.inr ⟨hS, h'⟩

theorem ggTableBNbrInnerInputOn_round10_of_round10Ns
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound10NsLabel) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound10Label :=
  ggTableBNbrInnerInputOn_of_not_orthNs h

theorem ggLNoInvariantLineInputOn_of_not_orthNs {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLNoInvariantLineInputOn fun p lab => S p lab ∧ ¬ GGOrthNsLabel p lab) :
    GGLNoInvariantLineInputOn S := by
  have h' := ggLNoInvariantLineInputOn_orthNs.or h
  intro G _ _ p B Bs x L D J hC hL
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)
  by_cases h1 : GGOrthNsLabel p lab
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩

theorem ggLNoInvariantLineInputOn_lineRest_of_lineRestNs
    (h : GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRestNsLabel) :
    GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRestLabel :=
  ggLNoInvariantLineInputOn_of_not_orthNs h

end FromLID

theorem ggLNoInvariantLineInputOn_lineRestNs_of_lineRest
    (h : GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRestLabel) :
    GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRestNsLabel := by
  intro G _ _ p B Bs x L D J hC hL
  exact h G p B Bs x L D J hC (hL.mono fun _ _ h => h.1)

theorem ggTableBNbrInnerInputOn_round10Ns_of_round10
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound10Label) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound10NsLabel :=
  h.mono fun _ _ h11 => h11.1

theorem ggTableBCxInputOn_rest2Ns_of_rest2
    (h : GGTableBCxInputOn GGCorFourTwoOpenTableBRest2Label) :
    GGTableBCxInputOn GGCorFourTwoOpenTableBRest2NsLabel :=
  h.mono fun _ _ h => h.1

theorem ggTableBModuleInputOn_rest2Ns_of_rest2
    (h : GGTableBModuleInputOn GGCorFourTwoOpenTableBRest2Label) :
    GGTableBModuleInputOn GGCorFourTwoOpenTableBRest2NsLabel :=
  h.mono fun _ _ h => h.1

theorem ggTableBActionInputOn_rest2Ns_of_rest2
    (h : GGTableBActionInputOn GGCorFourTwoOpenTableBRest2Label) :
    GGTableBActionInputOn GGCorFourTwoOpenTableBRest2NsLabel :=
  h.mono fun _ _ h => h.1

section Certs


theorem ggTableBCxInputOn_of_not_orthNsVac {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGOrthNsVacLabel p lab) :
    GGTableBCxInputOn S :=
  ((ggTableBCxInputOn_orthNsVac ggLNoncyclicInput_holds).or h).mono fun p lab hS => by
    by_cases h3 : GGOrthNsVacLabel p lab
    · exact Or.inl h3
    · exact Or.inr ⟨hS, h3⟩

theorem ggTableBCxInputOn_rest2_of_rest2Ns
    (h : GGTableBCxInputOn GGCorFourTwoOpenTableBRest2NsLabel) :
    GGTableBCxInputOn GGCorFourTwoOpenTableBRest2Label :=
  ggTableBCxInputOn_of_not_orthNsVac h

theorem ggTableBModuleInputOn_of_not_orthNsVac {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGOrthNsVacLabel p lab) :
    GGTableBModuleInputOn S :=
  ((ggTableBModuleInputOn_orthNsVac ggLNoncyclicInput_holds).or h).mono fun p lab hS => by
    by_cases h3 : GGOrthNsVacLabel p lab
    · exact Or.inl h3
    · exact Or.inr ⟨hS, h3⟩

theorem ggTableBModuleInputOn_rest2_of_rest2Ns
    (h : GGTableBModuleInputOn GGCorFourTwoOpenTableBRest2NsLabel) :
    GGTableBModuleInputOn GGCorFourTwoOpenTableBRest2Label :=
  ggTableBModuleInputOn_of_not_orthNsVac h

theorem ggTableBActionInputOn_of_not_orthNsVac {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGOrthNsVacLabel p lab) :
    GGTableBActionInputOn S :=
  ((ggTableBActionInputOn_orthNsVac ggLNoncyclicInput_holds).or h).mono fun p lab hS => by
    by_cases h3 : GGOrthNsVacLabel p lab
    · exact Or.inl h3
    · exact Or.inr ⟨hS, h3⟩

theorem ggTableBActionInputOn_rest2_of_rest2Ns
    (h : GGTableBActionInputOn GGCorFourTwoOpenTableBRest2NsLabel) :
    GGTableBActionInputOn GGCorFourTwoOpenTableBRest2Label :=
  ggTableBActionInputOn_of_not_orthNsVac h


theorem ggTableBCxInput_of_openRest2Ns (h : GGTableBCxInputOn GGCorFourTwoOpenTableBRest2NsLabel) :
    GGTableBCxInput :=
  ggTableBCxInput_of_openRest2 (ggTableBCxInputOn_rest2_of_rest2Ns h)

theorem ggTableBModuleInput_of_openRest2Ns
    (h : GGTableBModuleInputOn GGCorFourTwoOpenTableBRest2NsLabel) : GGTableBModuleInput :=
  ggTableBModuleInput_of_openRest2 (ggTableBModuleInputOn_rest2_of_rest2Ns h)

theorem ggTableBActionInput_of_openRest2Ns
    (h : GGTableBActionInputOn GGCorFourTwoOpenTableBRest2NsLabel) : GGTableBActionInput :=
  ggTableBActionInput_of_openRest2 (ggTableBActionInputOn_rest2_of_rest2Ns h)

theorem ggCor42Input_of_openRestNs (hK : GGKantorReductionInput)
    (hLID : GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRestLabel)
    (hcen : GGLTransvectionCenterInputOn GGCorFourTwoOpenLabel)
    (hline : GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRestNsLabel)
    (hnorm : GGBstarNbrNormalInput) (hgraph : GGNbrGraphInput)
    (hfield : GGNbrFieldTransvectionInput) : GGCor42Input :=
  ggCor42Input_of_openRest hK hLID hcen (ggLNoInvariantLineInputOn_lineRest_of_lineRestNs hline)
    hnorm hgraph hfield

theorem ggNoTransvectionInput_of_openRestNs (hK : GGKantorReductionInput)
    (hLID : GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRestLabel)
    (hcen : GGLTransvectionCenterInputOn GGCorFourTwoOpenLabel)
    (hline : GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRestNsLabel) :
    GGNoTransvectionInput :=
  ggNoTransvectionInput_of_openRest hK hLID hcen
    (ggLNoInvariantLineInputOn_lineRest_of_lineRestNs hline)

theorem ggTableBNbrInnerInputOn_round6_of_round10Ns
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound10NsLabel) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound6Label :=
  ggTableBNbrInnerInputOn_round6_of_round10 (ggTableBNbrInnerInputOn_round10_of_round10Ns h)

theorem ggTableBNbrInnerInput_of_round10Ns
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound10NsLabel) : GGTableBNbrInnerInput :=
  ggTableBNbrInnerInput_of_round10 (ggTableBNbrInnerInputOn_round10_of_round10Ns h)

end Certs

end CFSG.StandardType

end
