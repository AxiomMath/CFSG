module

public import CFSG.OddTranspositions.PartThree.Statements

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

@[expose] def Theorem8_5At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ D : Set G, HypothesisC D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → ¬ O4PairData G D →
    ∀ u w v : G, IsTriangle D u w v → IsThirdKind u w v →
      ∃ d ∈ D, Commute d u ∧ Commute d v ∧ Commute d w

theorem theorem8_5_iff : Theorem8_5 ↔ ∀ (G : Type) [Group G] [Finite G], Theorem8_5At G :=
  Iff.rfl

end CFSG.OddTranspositions.PartThree
