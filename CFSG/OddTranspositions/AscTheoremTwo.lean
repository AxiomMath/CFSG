module

public import CFSG.OddTranspositions.O4CloseReduction

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

@[expose] def AschbacherTheoremTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G),
    Setup G D → HypothesisC D → LocalSecond D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) ∨ O4PairData G D

end CFSG.OddTranspositions
