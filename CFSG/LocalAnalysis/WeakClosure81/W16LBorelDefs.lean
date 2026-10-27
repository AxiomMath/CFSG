module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LargeExtraspecial.S9TIInput

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

@[expose] def Borel166Conclusion {X : Type} [Group X] (Y P : Subgroup X) : Prop :=
  ∃ h : X, h ∈ normalizer (Y : Set X) ∧ h ∈ normalizer (P : Set X) ∧ Odd (orderOf h) ∧
    (∀ P₀ : Subgroup X, Y ≤ P₀ → P₀ ≤ P → (∀ x ∈ P₀, h * x * h⁻¹ ∈ P₀) → P₀ = Y ∨ P₀ = P) ∧
    (∀ x ∈ P, h * x * h⁻¹ * x⁻¹ ∈ Y → x ∈ Y)

end CFSG.LocalAnalysis.WeakClosure81

end
