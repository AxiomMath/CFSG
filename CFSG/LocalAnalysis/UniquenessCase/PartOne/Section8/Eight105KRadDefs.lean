module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def RadicalFacts (X : Type) [Group X] [Finite X] (B₀ : Subgroup X) : Prop :=
  ∃ Y₁ Y₂ : Subgroup X,
    (∀ Y ∈ ({Y₁, Y₂} : Set (Subgroup X)),
      Y ≠ ⊤ ∧ (∃ T₀ : Sylow 2 X, normalizer ((T₀ : Subgroup X) : Set X) ≤ Y) ∧
        centralizer (B₀ : Set X) ≤ Y ∧ pCoreOf 2 Y ≠ ⊥ ∧
        F08.KOf8103 ⊤ B₀ ⊓ pCoreOf 2 Y = ⊥ ∧
        ∀ T₀ : Sylow 2 X, pCoreOf 2 Y ≤ (T₀ : Subgroup X) →
          normalizer ((T₀ : Subgroup X) : Set X) ≤ Y) ∧
      pCoreOf 2 Y₁ ⊓ Y₂ = ⊥ ∧ pCoreOf 2 Y₂ ⊓ Y₁ = ⊥ ∧
      ∀ Z : Subgroup X, Z ≠ ⊤ →
        (∃ T₀ : Sylow 2 X, normalizer ((T₀ : Subgroup X) : Set X) ≤ Z) →
          F08.KOf8103 ⊤ B₀ ⊔ B₀ ≤ Z → Z = Y₁ ∨ Z = Y₂

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
