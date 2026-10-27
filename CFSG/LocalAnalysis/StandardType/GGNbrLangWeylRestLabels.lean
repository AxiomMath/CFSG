module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangWeylRestSL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrLangRest12Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrLangRestLabel p lab ∧ ¬ GGNbrLangE6CoprimeLabel p lab ∧ lab.tag ≠ .twB2

@[expose] def GGNbrWeylRest12Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylRestLabel p lab ∧ ¬ GGNbrWeylVacLabel p lab ∧ ¬ GGNbrLinearNsLabel p lab

theorem ggNbrInnerWeylOn_rest_of_rest12
    (h : GGNbrInnerWeylOn GGNbrWeylRest12Label) :
    GGNbrInnerWeylOn GGNbrWeylRestLabel := by
  refine ((h.or ggNbrInnerWeylOn_vac).or ggNbrInnerWeylOn_linearNs).mono ?_
  intro p lab hS
  by_cases h1 : GGNbrWeylVacLabel p lab
  · exact Or.inl (Or.inr h1)
  by_cases h2 : GGNbrLinearNsLabel p lab
  · exact Or.inr h2
  exact Or.inl (Or.inl ⟨hS, h1, h2⟩)

end CFSG.StandardType

end
