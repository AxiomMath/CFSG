module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreSp
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreVac
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreOrth
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem GGTableBCxInputOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hSS' : ∀ p lab, S p lab → S' p lab) (h : GGTableBCxInputOn S') : GGTableBCxInputOn S :=
  fun G _ _ p B Bs x L D J hcfg hM => h G p B Bs x L D J hcfg (hM.mono hSS')

theorem GGTableBModuleInputOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hSS' : ∀ p lab, S p lab → S' p lab) (h : GGTableBModuleInputOn S') :
    GGTableBModuleInputOn S :=
  fun G _ _ p B Bs x L D J hcfg hM => h G p B Bs x L D J hcfg (hM.mono hSS')

theorem GGTableBActionInputOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hSS' : ∀ p lab, S p lab → S' p lab) (h : GGTableBActionInputOn S') :
    GGTableBActionInputOn S :=
  fun G _ _ p B Bs x L D J B₂ hcfg hM => h G p B Bs x L D J B₂ hcfg (hM.mono hSS')

@[expose] def GGCorFourTwoTableBMoreLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGSpTwoThreeLabel p lab ∨ GGCorFourTwoTableBVacLabel p lab ∨ GGCorFourTwoOrthSplitLabel p lab

@[expose] def GGCorFourTwoOpenTableBRest2Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenTableBRestLabel p lab ∧ ¬ GGCorFourTwoTableBMoreLabel p lab

section More


theorem ggTableBCxInputOn_more : GGTableBCxInputOn GGCorFourTwoTableBMoreLabel :=
  ((ggTableBCxInputOn_spTwoThree.or ggCorFourTwoInputsOn_tableBVac.2.2.2.1).or
    ggTableBCxInputOn_orthSplit).mono fun _ _ h => by
      rcases h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem ggTableBModuleInputOn_more : GGTableBModuleInputOn GGCorFourTwoTableBMoreLabel :=
  ((ggTableBModuleInputOn_spTwoThree.or ggCorFourTwoInputsOn_tableBVac.2.2.2.2.1).or
    ggTableBModuleInputOn_orthSplit).mono fun _ _ h => by
      rcases h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem ggTableBActionInputOn_more : GGTableBActionInputOn GGCorFourTwoTableBMoreLabel :=
  ((ggTableBActionInputOn_spTwoThree.or ggCorFourTwoInputsOn_tableBVac.2.2.2.2.2).or
    ggTableBActionInputOn_orthSplit).mono fun _ _ h => by
      rcases h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem ggTableBCxInputOn_rest_of_rest2
    (h : GGTableBCxInputOn GGCorFourTwoOpenTableBRest2Label) :
    GGTableBCxInputOn GGCorFourTwoOpenTableBRestLabel :=
  (ggTableBCxInputOn_more.or h).mono fun p lab h1 => by
    by_cases h2 : GGCorFourTwoTableBMoreLabel p lab
    · exact Or.inl h2
    · exact Or.inr ⟨h1, h2⟩

theorem ggTableBModuleInputOn_rest_of_rest2
    (h : GGTableBModuleInputOn GGCorFourTwoOpenTableBRest2Label) :
    GGTableBModuleInputOn GGCorFourTwoOpenTableBRestLabel :=
  (ggTableBModuleInputOn_more.or h).mono fun p lab h1 => by
    by_cases h2 : GGCorFourTwoTableBMoreLabel p lab
    · exact Or.inl h2
    · exact Or.inr ⟨h1, h2⟩

theorem ggTableBActionInputOn_rest_of_rest2
    (h : GGTableBActionInputOn GGCorFourTwoOpenTableBRest2Label) :
    GGTableBActionInputOn GGCorFourTwoOpenTableBRestLabel :=
  (ggTableBActionInputOn_more.or h).mono fun p lab h1 => by
    by_cases h2 : GGCorFourTwoTableBMoreLabel p lab
    · exact Or.inl h2
    · exact Or.inr ⟨h1, h2⟩

end More

theorem ggTableBCxInputOn_rest2_of_rest (h : GGTableBCxInputOn GGCorFourTwoOpenTableBRestLabel) :
    GGTableBCxInputOn GGCorFourTwoOpenTableBRest2Label :=
  h.mono fun _ _ h => h.1

theorem ggTableBModuleInputOn_rest2_of_rest
    (h : GGTableBModuleInputOn GGCorFourTwoOpenTableBRestLabel) :
    GGTableBModuleInputOn GGCorFourTwoOpenTableBRest2Label :=
  h.mono fun _ _ h => h.1

theorem ggTableBActionInputOn_rest2_of_rest
    (h : GGTableBActionInputOn GGCorFourTwoOpenTableBRestLabel) :
    GGTableBActionInputOn GGCorFourTwoOpenTableBRest2Label :=
  h.mono fun _ _ h => h.1

section Certs


theorem ggTableBCxInput_of_openRest2 (h : GGTableBCxInputOn GGCorFourTwoOpenTableBRest2Label) :
    GGTableBCxInput :=
  ggTableBCxInput_of_openRest (ggTableBCxInputOn_rest_of_rest2 h)

theorem ggTableBModuleInput_of_openRest2
    (h : GGTableBModuleInputOn GGCorFourTwoOpenTableBRest2Label) : GGTableBModuleInput :=
  ggTableBModuleInput_of_openRest (ggTableBModuleInputOn_rest_of_rest2 h)

theorem ggTableBActionInput_of_openRest2
    (h : GGTableBActionInputOn GGCorFourTwoOpenTableBRest2Label) : GGTableBActionInput :=
  ggTableBActionInput_of_openRest (ggTableBActionInputOn_rest_of_rest2 h)

end Certs

end CFSG.StandardType

end
