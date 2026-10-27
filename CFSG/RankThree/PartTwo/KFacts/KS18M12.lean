module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.KFacts

@[expose] def KS18M12 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) →
    3 ∣ Nat.card X ∧ Subgroup.center X = ⊥ ∧
    (∀ σ : MulAut X, (∃ k : ℕ, σ ^ 3 ^ k = 1) → ∃ x : X, σ = MulAut.conj x) ∧
    ∀ N : Subgroup X, N.Normal → Group.IsSolvable N → N = ⊥

end CFSG.RankThree.PartTwo.KFacts
