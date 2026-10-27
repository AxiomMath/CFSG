module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Is3D4)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def K_3D4TwoAut : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Is3D4 X 1 →
    Subgroup.center X = ⊥ ∧ IsCyclic (Outer X) ∧ Nat.card (Outer X) = 3

@[expose] def K_3D4TwoThreeRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Is3D4 X 1 → CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2

@[expose] def K_3D4TwoSmallRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Is3D4 X 1 → ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → p ≠ 7 →
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1

@[expose] def K_3D4TwoSylowSeven : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Is3D4 X 1 → ∀ P : Sylow 7 X,
    CFSG.Open.IsElemAbelian 7 (P : Subgroup X) ∧ Nat.card (P : Subgroup X) = 49

@[expose] def K_3D4TwoBorel : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y U : Subgroup A), Is3D4 ↥Y 1 →
    CFSG.QuasithinUnique.IsSylowTwoOf U Y →
      7 ∣ Nat.card ↥(Y ⊓ Subgroup.normalizer (U : Set A)) ∧
      ∀ r ∈ Subgroup.normalizer (Y : Set A) ⊓ Subgroup.normalizer (U : Set A),
        ∃ j : ℕ, ∀ b ∈ Y ⊓ Subgroup.normalizer (U : Set A),
          r * b * r⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
