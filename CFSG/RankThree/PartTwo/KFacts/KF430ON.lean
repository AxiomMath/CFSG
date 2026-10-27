module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree.PartTwo.Sec4 (IsTripleCover)

@[expose] def KF430ON : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (A L : Subgroup M) (a c : M),
    CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 27 →
    (∀ x : M, x ^ 3 = 1 → (∀ y ∈ A, x * y = y * x) → x ∈ A) →
    A ≤ Subgroup.normalizer (L : Set M) → Group.IsPerfect ↥L →
    IsTripleCover ↥L CFSG.Blueprint.NativeSporadic.ON →
    A ⊓ Subgroup.centralizer (L : Set M) = Subgroup.zpowers a → orderOf a = 3 →
    c ∈ A → c ∉ Subgroup.zpowers a →
    L ⊓ Subgroup.normalizer (A : Set M) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set M) →
    False

end CFSG.RankThree.PartTwo.KFacts
