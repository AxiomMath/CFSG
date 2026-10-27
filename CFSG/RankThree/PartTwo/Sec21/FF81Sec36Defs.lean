module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

def torElt {X : Type} [Group X] (b₁ b₂ b₃ : X) (x : Fin 3 → ZMod 3) : X :=
  b₁ ^ (x 0).val * b₂ ^ (x 1).val * b₃ ^ (x 2).val

def torWt (x : Fin 3 → ZMod 3) : ℕ :=
  (if x 0 ≠ 0 then 1 else 0) + (if x 1 ≠ 0 then 1 else 0) + (if x 2 ≠ 0 then 1 else 0)

def KF_Sp6RefS : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), StatedClassicalModel ↥L .PSp 3 2 1 →
    ∀ b₁ b₂ b₃ : X, b₁ ∈ L → b₂ ∈ L → b₃ ∈ L → IsElemAb 3 3 (Subgroup.closure {b₁, b₂, b₃}) →
    L ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) = Subgroup.closure {b₁, b₂, b₃} →
    (∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₁, b₂, b₃}) → ∀ x ∈ ({b₁, b₂, b₃} : Set X),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set X)) →
    ∀ s ∈ L, orderOf s = 2 → s ∈ Nor (Subgroup.closure {b₁, b₂, b₃}) →
    ∀ x y : Fin 3 → ZMod 3, x ≠ 0 → (∀ c : ZMod 3, y ≠ c • x) →
      s * torElt b₁ b₂ b₃ x = torElt b₁ b₂ b₃ x * s →
      s * torElt b₁ b₂ b₃ y = torElt b₁ b₂ b₃ y * s →
      (torWt x = 2 → Nat.card (Op 2 (L ⊓ Cen s ⊓ Cen (torElt b₁ b₂ b₃ x))) ≤ 2) ∧
      (torWt x = 1 → Nat.card (Op 2 (L ⊓ Cen s ⊓ Cen (torElt b₁ b₂ b₃ x))) = 8 ∧
        (∀ u ∈ Op 2 (L ⊓ Cen s ⊓ Cen (torElt b₁ b₂ b₃ x)),
          ∀ v ∈ Op 2 (L ⊓ Cen s ⊓ Cen (torElt b₁ b₂ b₃ x)), u * v = v * u) ∧
        ∀ u ∈ Op 2 (L ⊓ Cen s ⊓ Cen (torElt b₁ b₂ b₃ x)), u * u = 1) ∧
      (torWt x = 3 → Nat.card (Op 2 (L ⊓ Cen s ⊓ Cen (torElt b₁ b₂ b₃ x))) = 8 ∧
        ∃ u ∈ Op 2 (L ⊓ Cen s ⊓ Cen (torElt b₁ b₂ b₃ x)),
          ∃ v ∈ Op 2 (L ⊓ Cen s ⊓ Cen (torElt b₁ b₂ b₃ x)), u * v ≠ v * u)

def KF_Sp6SL3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), StatedClassicalModel ↥L .PSp 3 2 1 →
    ∀ b₁ b₂ b₃ : X, b₁ ∈ L → b₂ ∈ L → b₃ ∈ L → IsElemAb 3 3 (Subgroup.closure {b₁, b₂, b₃}) →
    L ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) = Subgroup.closure {b₁, b₂, b₃} →
    (∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₁, b₂, b₃}) → ∀ x ∈ ({b₁, b₂, b₃} : Set X),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set X)) →
    ∃ K : Subgroup X, K ≤ L ∧ Nonempty (↥K ≃* GL (Fin 3) (ZMod 2)) ∧ b₁ * b₂ ∈ K

def KF_SL32Fix : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K U W : Subgroup X), Nonempty (↥K ≃* GL (Fin 3) (ZMod 2)) →
    IsPGroup 2 U → W ≤ U → (∀ u ∈ U, ∀ w ∈ W, u * w * u⁻¹ ∈ W) → K ≤ Nor U → K ≤ Nor W →
    ∀ y ∈ K, orderOf y = 3 →
      Nat.card U * Nat.card ↥(W ⊓ Cen y) ^ 4 ≤ Nat.card W * Nat.card ↥(U ⊓ Cen y) ^ 4

end CFSG.RankThree.PartTwo.Sec21.FF81
