module

public import CFSG.OddTranspositions.SevenThreeConjOrder
public import CFSG.OddTranspositions.FiveThreeQZ

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem sevenThree
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hL : LocalSecond D)
    (h3 : ∀ w ∈ AalphaStar D hC.alpha, orderOf (hC.d * w) = 3)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) :
    ∃ w ∈ AalphaStar D hC.alpha, orderOf (hC.d * w) ≠ 3 :=
  sevenThree_of_faithful_of_base hC h3
    (QZ.faithfulOnBlocks_of_localSecond hC hrad hL) hnot3

end CFSG.OddTranspositions

