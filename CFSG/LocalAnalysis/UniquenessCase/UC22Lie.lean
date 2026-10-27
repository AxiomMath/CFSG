module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.Milestones.ASVolI.A2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def ActsNontrivOnDiagram (L : Subgroup G) (x : G) : Prop :=
  x ∈ normalizer (L : Set G) ∧
    ∃ θ : MulAut (Bar2 L ⧸ Subgroup.center (Bar2 L)), InducedQuot L x θ ∧
      ¬ CFSG.ASVolI.ChA.IsInnDiagFieldAut _ θ

@[expose] def ActsNontrivOnDiagramIn {Y : Type} [Group Y] (X : Subgroup Y) (x : Y) : Prop :=
  x ∈ normalizer (X : Set Y) ∧
    ∃ θ : MulAut (↥X ⧸ Subgroup.center ↥X),
      (∀ a a' : ↥X, (a' : Y) = x * (a : Y) * x⁻¹ → θ (QuotientGroup.mk a) = QuotientGroup.mk a') ∧
        ¬ CFSG.ASVolI.ChA.IsInnDiagFieldAut _ θ

end CFSG.LocalAnalysis.UniquenessCase.UC22
