module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148D

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

@[expose] def ONTripleGenE27 : Prop :=
  ∀ (M : Type) [Group M] [Finite M], Group.IsPerfect M →
    Sec4.IsTripleCover M CFSG.Blueprint.NativeSporadic.ON → ∀ E : Subgroup M, Late.IsE27 E → ∀ 𝒦 : Set (Subgroup M),
      (∀ u ∈ E, u ∉ Subgroup.center M → ∃ K ∈ 𝒦, K ≤ Subgroup.centralizer ({u} : Set M) ∧
        Group.IsPerfect ↥K ∧ 1080 ≤ Nat.card K ∧
        ¬ E ≤ Subgroup.centralizer ((K : Subgroup M) : Set M)) →
      sSup 𝒦 = ⊤

end CFSG.RankThree.PartTwo.Sec14.Ronan148D
