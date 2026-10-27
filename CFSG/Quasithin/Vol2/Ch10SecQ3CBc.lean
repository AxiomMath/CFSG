module

public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

@[expose] def FactBorelCartan : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), 2 ≤ n →
    (E2.IsBenderOf n Y ∨ IsPSL 3 2 n Y ∨ IsPSp4 2 n Y) →
    ∀ S : Subgroup Y, QuasithinUnique.IsSylowTwoOf S ⊤ →
      ∃ d : Y, d ∈ Subgroup.normalizer (S : Set Y) ∧ orderOf d = 2 ^ n - 1

end CFSG.Quasithin.Vol2.Ch10.SecB
