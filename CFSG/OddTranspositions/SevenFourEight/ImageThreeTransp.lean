module

public import CFSG.OddTranspositions.SevenFourEight.ImageConnectedThree
public import CFSG.OddTranspositions.SevenFourEight.NoAlmostSimpleImage

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity
open CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem threeTransp_imageClass
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hmin : SmallerTwoStar (Nat.card G)) :
    ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ) := by
  by_cases hHns : Group.IsSolvable ↥(Halpha D hC.alpha)
  ·
    intro x _ y _
    have htop : CFSG.solvableRadical ↥(Halpha D hC.alpha) = ⊤ :=
      top_le_iff.mp (CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
        (N := ⊤) inferInstance inferInstance)
    have h1 : ∀ z : ↥(Halpha D hC.alpha) ⧸ CFSG.solvableRadical ↥(Halpha D hC.alpha), z = 1 := by
      intro z
      obtain ⟨z0, rfl⟩ := QuotientGroup.mk_surjective z
      rw [QuotientGroup.eq_one_iff, htop]
      exact Subgroup.mem_top z0
    rw [h1 (x * y), orderOf_one]
    exact Set.mem_insert _ _
  by_cases hconn : Disconnected (imageClass hC)
  ·
    exfalso
    have hS := setup_quotient hC hHns
    have hsec : ∀ a b t, IsTriangle (imageClass hC) a b t → orderOf (a * t * b) = 4 :=
      fun _ _ _ h => orderOf_eq_four_of_isTriangle_imageClass hC
        (localSecond_of_forall_secondKind hsecond) hHns h
    exact not_almostSimpleCase_imageClass hC hrad hsecond hnot3 hmin hHns
      (almostSimpleCase_of_disconnected hS (solvable_normal_eq_bot_imageClass hC)
        (localSecond_of_forall_secondKind hsec)
        (not_meetsSq_of_secondKind hS (solvable_normal_eq_bot_imageClass hC) hsec) hconn)
  · exact threeTransp_imageClass_of_connected hC hrad hsecond hnot3 hmin hconn hHns

end CFSG.OddTranspositions

end
