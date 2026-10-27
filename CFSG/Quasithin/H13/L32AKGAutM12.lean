module

public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.H13

@[expose] def KGAutM12E16 : Prop :=
  ∀ (A : Type) [Group A] [Finite A], Nonempty (A ≃* MulAut ↥CFSG.Open.quasithinM12) →
    ∀ T U P : Subgroup A, Nat.card T = 2 ^ 7 → U ≤ T → T ≤ Subgroup.normalizer (U : Set A) →
      Nat.card U = 16 → (∀ u ∈ U, u ^ 2 = 1) → T ≤ P → P ≤ Subgroup.normalizer (U : Set A) →
      Nat.card P = 2 ^ 7 * 3 → U ⊓ Subgroup.centralizer (P : Set A) = ⊥

end CFSG.Quasithin.H13
