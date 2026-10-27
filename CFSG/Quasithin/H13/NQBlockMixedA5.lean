module

public import CFSG.LocalAnalysis.SteinbergCEIsotypicMultiplicity
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.H13.NQBlock

open Module

@[expose] def MixedA5RankBudget : Prop :=
  ∀ (S : Type) [AddCommGroup S] [Module (ZMod 2) S] [FiniteDimensional (ZMod 2) S] [Nontrivial S]
    (X D Y A : Subgroup (Module.End (ZMod 2) S)ˣ),
    (∀ x ∈ X, ∀ d ∈ D, x * d = d * x) →
    (∀ W : Submodule (ZMod 2) S,
      (∀ g ∈ X ⊔ D, ∀ v ∈ W, (g : Module.End (ZMod 2) S) v ∈ W) → W = ⊥ ∨ W = ⊤) →
    X ≠ ⊥ → Group.IsPerfect X →
    (∀ d ∈ D, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) → Nonempty (Y ≃* alternatingGroup (Fin 5)) →
    (∀ d ∈ D, (∀ y ∈ Y, d * y = y * d) → d = 1) →
    D = Y ⊔ A → A ≠ ⊥ → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
    ∀ j : ℕ, j ≤ 1 →
      j + Nat.log 2 (Nat.card A) <
        finrank (ZMod 2) S - finrank (ZMod 2) (CFSG.LocalAnalysis.CommutingFactor.fixedSub A)

end CFSG.Quasithin.H13.NQBlock
