module

public import CFSG.RankThree.GF2n.Smith81.Bridge

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Smith216OrthStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → OrthCase M Q Z B →
      ∀ z ∈ Z, z ≠ 1 → ∀ x z' w y : G, IsConj z x → IsConj z z' → IsConj z w → IsConj z y →
        Commute x z' → Commute z' w → Commute w y →
          ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y

end CFSG.RankThree.GF2n.Smith81
