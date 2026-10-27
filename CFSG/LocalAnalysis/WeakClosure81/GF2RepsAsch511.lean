module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt OInf)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (W4Lem4_10 W4Lem4_11)
open CFSG.Blueprint (LieModel)

theorem hasQuotShape_or {Q : Type} [Group Q] {K : Subgroup Q} {N : Set Q}
    {P₁ P₂ : ∀ (X : Type) [Group X], Prop} (h : HasQuotShape K N (fun X _ => P₁ X ∨ P₂ X)) :
    HasQuotShape K N P₁ ∨ HasQuotShape K N P₂ := by
  obtain ⟨X, hXg, φ, hφ, hker, hP⟩ := h
  rcases hP with hP | hP
  · exact Or.inl ⟨X, hXg, φ, hφ, hker, hP⟩
  · exact Or.inr ⟨X, hXg, φ, hφ, hker, hP⟩

end CFSG.LocalAnalysis.WeakClosure81
