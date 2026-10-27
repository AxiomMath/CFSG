module

public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup

open scoped Pointwise commutatorElement

@[expose] def Gap17_45_NonabComponent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L A₁ A₂ B T ML : Subgroup X),
    L.Normal → IsSimpleGroup L → ¬ IsMulCommutative L → CFSG.Open.IsKGroup L →
    centralizer (L : Set X) = ⊥ →
    Nat.card A₁ = 31 → Nat.card A₂ = 31 → A₁ ⊓ A₂ = ⊥ →
    A₁ ≤ centralizer (A₂ : Set X) →
    Nat.card B = 5 → B ≤ normalizer (A₁ : Set X) → B ≤ normalizer (A₂ : Set X) →
    ⁅A₁ ⊔ A₂, B⁆ = A₁ ⊔ A₂ →
    (∀ D : Subgroup X, D ≤ A₁ ⊔ A₂ → Nat.card D = 31 → B ≤ normalizer (D : Set X) →
      D = A₁ ∨ D = A₂) →
    IsPGroup 2 T →
    ((A₁ ⊔ A₂ : Subgroup X) : Set X) * (T : Set X) =
      (T : Set X) * ((A₁ ⊔ A₂ : Subgroup X) : Set X) →
    (B : Set X) * (T : Set X) = (T : Set X) * (B : Set X) →
    CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L →
    ML ≤ L → ML ≠ L → T ⊓ L ≤ ML →
    (∀ C : Subgroup X, IsMulCommutative C → (A₁ ≤ C ∨ A₂ ≤ C ∨ B ≤ C) →
      L ⊓ normalizer (C : Set X) ≤ ML) →
    (5 ∣ Nat.card L → CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 (ML.subgroupOf L)) →
    False

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
