module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.KFacts

@[expose] def KS166J2A5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ K : Subgroup X, Group.IsPerfect ↥K →
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) →
      ∀ E : Subgroup X, E ≤ Subgroup.normalizer (K : Set X) → (∀ x ∈ E, x ^ 3 = 1) →
        Nat.card E = 9 →
        CFSG.pCore 2 ↥K = ⊥ ∧
        Group.IsSolvable ↥(Subgroup.centralizer (K : Set X)) ∧
        (∀ α : MulAut X, (∀ k ∈ K, α k = k) →
          ∃ g ∈ Subgroup.centralizer (K : Set X), α = MulAut.conj g) ∧
        (∀ U : Subgroup X, U ≤ Subgroup.centralizer (K : Set X) → IsPGroup 2 U →
          E ≤ Subgroup.normalizer (U : Set X) →
            U = ⊥ ∨ U = CFSG.Open.pCoreOf 2 (Subgroup.centralizer (K : Set X))) ∧
        Nonempty (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (K : Set X)) ≃*
          Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
        Nonempty (Subgroup.centralizer
            ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer (K : Set X)) : Subgroup X) : Set X) ≃*
          (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5))

end CFSG.RankThree.PartTwo.KFacts
