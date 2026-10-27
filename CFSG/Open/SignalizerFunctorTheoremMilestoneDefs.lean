module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open
@[expose] def signalizerFunctorEk {G : Type*} [Group G] (p k : ℕ) (A : Subgroup G) :
    Set (Subgroup G) :=
  {S | S ≤ A ∧ Nat.card S = p ^ k}

end CFSG.Open
