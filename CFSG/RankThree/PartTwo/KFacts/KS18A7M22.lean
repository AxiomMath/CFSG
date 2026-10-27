module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.KFacts

@[expose] def KS18A7M22 : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) →
    3 ∣ Nat.card X ∧ Subgroup.center X = ⊥ ∧
    (∀ σ : MulAut X, (∃ k : ℕ, σ ^ 3 ^ k = 1) → ∃ x : X, σ = MulAut.conj x) ∧
    (∀ x : X, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ^ 3 = 1) ∧
    ∀ Q : Subgroup X, IsPGroup 3 Q → IsMulCommutative Q

end CFSG.RankThree.PartTwo.KFacts
