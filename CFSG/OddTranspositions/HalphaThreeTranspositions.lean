module

public import CFSG.OddTranspositions.ConfigWidth
public import CFSG.OddTranspositions.HalphaWidth
public import CFSG.OddTranspositions.HalphaCard
public import CFSG.OddTranspositions.O4PairTriple

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem three_transpositions_imageClass (hC : HypothesisC D)
    (hQ : Config D u w v z a K₁ S') (hmin : SmallerTwoStar (Nat.card G))
    (hconn : ¬ Disconnected (imageClass hC))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha)) :
    ∀ d ∈ imageClass hC, ∀ e ∈ imageClass hC,
      orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
  have hrad : ∀ N : Subgroup (Halpha D hC.alpha ⧸
      CFSG.solvableRadical (Halpha D hC.alpha)),
      N.Normal → Group.IsSolvable N → N = ⊥ := by
    intro N hN hNs
    have hle : N ≤ CFSG.solvableRadical
        (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
      OddTransp.le_solvableRadical hN hNs
    rw [solvableRadical_quotient_H hC] at hle
    exact le_bot_iff.mp hle
  have h := hmin (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
    (imageClass hC) (card_quotient_Halpha_lt hC hQ.rad) (setup_quotient hC hHns) hconn
    hrad (localSecond_imageClass hC hQ.local2 hHns)
  rcases h with h3 | hO4
  · exact h3
  · exfalso
    exact not_O4PairData_of_widthLe_two hO4 (widthLe_imageClass_two hC (widthLe_three_of_config hQ))

theorem fischerPair_imageClass (hC : HypothesisC D)
    (hQ : Config D u w v z a K₁ S') (hmin : SmallerTwoStar (Nat.card G))
    (hconn : ¬ Disconnected (imageClass hC))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha)) :
    CFSG.Blueprint.Fischer.Pair
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC) :=
  ⟨inferInstance, imageClass_isClass hC, imageClass_involutions hC hHns,
    three_transpositions_imageClass hC hQ hmin hconn hHns, imageClass_gen hC⟩

end CFSG.OddTranspositions
