module

public import CFSG.LieType.SeitzGeneration.ExcTorusCount
public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.E6

open scoped Matrix

section Toral


@[expose] def BigElemAbelianToralBar (τ : Tag) (p : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], ¬ p ∣ Nat.card K →
    ∀ A : Subgroup (ModGL τ (AlgebraicClosure K)), A ≤ adjointGroup τ (AlgebraicClosure K) →
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x ^ p = 1) →
      p ^ (τ.rank - 1) ≤ Nat.card A →
        ∃ g ∈ adjointGroup τ (AlgebraicClosure K),
          ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup τ (AlgebraicClosure K)

end Toral

section FixedRoot

@[expose] def HalfMaxFixedRoot (τ : Tag) (p : ℕ) : Prop :=
  ∀ w : WeylGroup τ,
    p ^ (τ.rank - 1) ≤ Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod p) • z} →
    Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod p) • z} < p ^ τ.rank →
    ∃ β : Fin τ.rank → ℤ, IsRoot τ β ∧ w • β = β

end FixedRoot

end ExcFramesHalf

end CFSG.StandardType
