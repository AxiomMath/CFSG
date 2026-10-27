module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.KFacts

@[expose] def KS166J2A5Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ K : Subgroup X, Group.IsPerfect ↥K →
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) →
      ∀ E : Subgroup X, E ≤ Subgroup.normalizer (K : Set X) → (∀ x ∈ E, x ^ 3 = 1) →
        Nat.card E = 9 →
        ∀ x ∈ E, (∃ S : Sylow 3 X, x ∈ (S : Subgroup X) ∧
          (S : Subgroup X) ≤ Subgroup.centralizer {x}) →
        x ∈ Subgroup.centralizer (K : Set X)

end CFSG.RankThree.PartTwo.KFacts
