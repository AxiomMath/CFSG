module

public import CFSG.OddTranspositions.SevenFourEight.ImageSecondKind
public import CFSG.OddTranspositions.SevenFourEight.SecondKindConclusion
public import CFSG.OddTranspositions.HalphaCard
import CFSG.OddTranspositions.SevenFourEight.O4Triangle
public import CFSG.OddTranspositions.O4CloseReduction

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity
open CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem solvable_normal_eq_bot_imageClass (hC : HypothesisC D) :
    ∀ N : Subgroup (↥(Halpha D hC.alpha) ⧸ CFSG.solvableRadical ↥(Halpha D hC.alpha)),
      N.Normal → Group.IsSolvable N → N = ⊥ := fun _ hN hs =>
  le_bot_iff.mp ((solvableRadical_quotient_H hC) ▸
    CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical hN hs)

theorem threeTransp_imageClass_of_connected
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hmin : SmallerTwoStar (Nat.card G))
    (hconn : ¬ Disconnected (imageClass hC)) (hHns : ¬ Group.IsSolvable ↥(Halpha D hC.alpha)) :
    ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ) := by
  have _ := hnot3
  have hsec : ∀ x y t, IsTriangle (imageClass hC) x y t → orderOf (x * t * y) = 4 :=
    fun _ _ _ h => orderOf_eq_four_of_isTriangle_imageClass hC
      (localSecond_of_forall_secondKind hsecond) hHns h
  rcases hmin _ _ (card_quotient_Halpha_lt hC hrad) (setup_quotient hC hHns) hconn
      (solvable_normal_eq_bot_imageClass hC) (localSecond_of_forall_secondKind hsec) with h | h
  · exact h
  · obtain ⟨a, b, c, htri, hne⟩ := exists_triangle_ne_four_of_o4PairData h
    exact (hne (hsec a b c htri)).elim

end CFSG.OddTranspositions

end
