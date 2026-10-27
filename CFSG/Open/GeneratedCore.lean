module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open

variable {G : Type*} [Group G]

@[expose] noncomputable def GLBCore [Finite G] (p k : ℕ) (P : Subgroup G) : Subgroup G :=
  sSup {N | ∃ Q : Subgroup G, Q ≤ P ∧ k ≤ pRank p Q ∧ N = Subgroup.normalizer (Q : Set G)}

@[expose] noncomputable def rankThreeAschCore [Finite G] (k p : ℕ) (P : Subgroup G) : Subgroup G :=
  sSup {N | ∃ X : Subgroup G, X ≤ P ∧ k ≤ pRank p X ∧
    3 ≤ pRank p (X ⊔ (P ⊓ Subgroup.centralizer (X : Set G))) ∧
    N = Subgroup.normalizer (X : Set G)}

end CFSG.Open
