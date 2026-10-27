module

public import CFSG.Quasithin.EmptyFaithful.S151S8C1

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def ThreeDLocFor (K : TauCeti.SporadicName) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G), IsSporadic K ↥L → IsPGroup 2 ↥S →
    S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L →
    ∀ z ∈ centerOf (S ⊓ L), ¬ L ≤ Subgroup.centralizer ({z} : Set G) →
      ∃ P : Subgroup G, P ≤ L ∧ S ⊓ L ≤ P ∧ S ≤ Subgroup.normalizer (P : Set G) ∧
        ¬ P ≤ Subgroup.centralizer ({z} : Set G) ∧ CharTwo P ∧
        IsMinParabolicOf (P ⊔ S) (P ⊔ S) ∧ NumC126 (P ⊔ S) ∧
        oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P

end CFSG.Quasithin.S151S9T
