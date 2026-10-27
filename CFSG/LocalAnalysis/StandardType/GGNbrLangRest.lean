module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRestExc
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrLangRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ GGTypeASplitCoprimeLabel p lab ∧ ¬ GGLinearTwoLabel lab ∧ ¬ GGCorFourTwoOpenVacLabel p lab ∧
    ¬ GGNbrLangFieldTwoLabel lab ∧ ¬ GGLinearCoprimeDegLabel p lab ∧
    ¬ GGSpOmegaCoprimeDegLabel p lab ∧ ¬ GGExcCoprimeDegLabel p lab

@[expose] def GGNbrWeylRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ GGTypeASplitCoprimeLabel p lab ∧ ¬ GGLinearTwoLabel lab

theorem ggNbrLangTorusAxisOn_notTypeASplit_of_rest
    (h : GGNbrLangTorusAxisOn GGNbrLangRestLabel) :
    GGNbrLangTorusAxisOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab := by
  refine ((((((h.or ggNbrLangTorusAxisOn_linearTwo).or ggNbrLangTorusAxisOn_openVac).or
    ggNbrLangTorusAxisOn_fieldTwo).or ggNbrLangTorusAxisOn_linearCoprimeDeg).or
    ggNbrLangTorusAxisOn_spOmegaCoprimeDeg).or ggNbrLangTorusAxisOn_excCoprimeDeg).mono ?_
  intro p lab hS
  by_cases h1 : GGLinearTwoLabel lab
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1)))))
  by_cases h2 : GGCorFourTwoOpenVacLabel p lab
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h2))))
  by_cases h3 : GGNbrLangFieldTwoLabel lab
  · exact Or.inl (Or.inl (Or.inl (Or.inr h3)))
  by_cases h4 : GGLinearCoprimeDegLabel p lab
  · exact Or.inl (Or.inl (Or.inr h4))
  by_cases h5 : GGSpOmegaCoprimeDegLabel p lab
  · exact Or.inl (Or.inr h5)
  by_cases h6 : GGExcCoprimeDegLabel p lab
  · exact Or.inr h6
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hS, h1, h2, h3, h4, h5, h6⟩)))))

theorem ggNbrInnerWeylOn_notTypeASplit_of_rest (h : GGNbrInnerWeylOn GGNbrWeylRestLabel) :
    GGNbrInnerWeylOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab := by
  refine (h.or ggNbrInnerWeylOn_linearTwo).mono ?_
  intro p lab hS
  by_cases h1 : GGLinearTwoLabel lab
  · exact Or.inr h1
  · exact Or.inl ⟨hS, h1⟩

theorem ggNbrLangTorusAxisOn_rest_of_notTypeASplit
    (h : GGNbrLangTorusAxisOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab) :
    GGNbrLangTorusAxisOn GGNbrLangRestLabel :=
  h.mono fun _ _ hS => hS.1

theorem ggNbrInnerWeylOn_rest_of_notTypeASplit
    (h : GGNbrInnerWeylOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab) :
    GGNbrInnerWeylOn GGNbrWeylRestLabel :=
  h.mono fun _ _ hS => hS.1

end CFSG.StandardType

end
