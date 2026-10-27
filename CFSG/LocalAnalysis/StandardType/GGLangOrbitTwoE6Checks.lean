module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcDiagramAutomorphisms
public import CFSG.LocalAnalysis.StandardType.GGLatDefs

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem e6_iform_self_check : ∀ α ∈ rootFinset Tag.E6, iform α α = 2 := by
  decide +kernel

theorem e6_iform_trichotomy_check :
    ∀ α ∈ rootFinset Tag.E6, ∀ β ∈ rootFinset Tag.E6, (β ≠ α ∧ β ≠ -α) →
      (iform α β = 0 ∨ iform α β = 1 ∨ iform α β = -1) := by
  decide +kernel

theorem e6_sigmaOrth_A2_closed_check :
    ∀ α ∈ rootFinset Tag.E6, ∀ β ∈ rootFinset Tag.E6,
      (iform α β = -1 ∧ iform α (latPerm excDiagramSigmaE6 α) = 0 ∧
        iform α (latPerm excDiagramSigmaE6 β) = 0 ∧ iform β (latPerm excDiagramSigmaE6 α) = 0 ∧
        iform β (latPerm excDiagramSigmaE6 β) = 0) →
      ∀ y ∈ rootFinset Tag.E6,
        (y ≠ α ∧ y ≠ β ∧ y ≠ α + β ∧ y ≠ -α ∧ y ≠ -β ∧ y ≠ -(α + β) ∧
          iform α (latPerm excDiagramSigmaE6 y) = 0 ∧ iform β (latPerm excDiagramSigmaE6 y) = 0 ∧
          iform y (latPerm excDiagramSigmaE6 α) = 0 ∧ iform y (latPerm excDiagramSigmaE6 β) = 0 ∧
          iform y (latPerm excDiagramSigmaE6 y) = 0) →
        (iform α y = 0 ∧ iform β y = 0) := by
  decide +kernel

end CFSG.StandardType.LangRat
