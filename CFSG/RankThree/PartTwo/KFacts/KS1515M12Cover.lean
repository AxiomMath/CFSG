module

public import CFSG.RankThree.PartTwo.Sec4.Notation
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.KFacts

@[expose] def KS1515M12Cover : Prop :=
  ∀ (M : Type) [Group M] [Finite M], Nonempty (M ≃* CFSG.Blueprint.NativeSporadic.M12) →
    ∀ B X : Subgroup M, CFSG.Assembly.IsElemAbelian 3 B → Nat.card B = 9 →
      Nonempty (Sec4.autIn ⊤ B ≃* Equiv.Perm (Fin 3)) →
      Group.IsPerfect ↥X → X ≠ ⊥ → B ≤ Subgroup.normalizer (X : Set M) → X = ⊤

end CFSG.RankThree.PartTwo.KFacts
