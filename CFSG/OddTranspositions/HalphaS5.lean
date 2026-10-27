module

public import CFSG.Fischer.Classification.WidthTwoAssembly
public import CFSG.OddTranspositions.HalphaCommutatorSimple
public import CFSG.OddTranspositions.QuotientSolvable
public import CFSG.OddTranspositions.HalphaNonsolvable

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.OddTranspositions.QZ CFSG.Timmesfeld.Connectivity CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G] {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem imageClass_S5
    (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (hmin : SmallerTwoStar (Nat.card G)) (hconn : ¬ Disconnected (imageClass hC))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha)) :
    ∃ e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
        Equiv.Perm (Fin 5),
      e '' imageClass hC = transpositions := by
  have hP : CFSG.Blueprint.Fischer.Pair
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC) :=
    fischerPair_imageClass hC hQ hmin hconn hHns
  have hZ : Subgroup.center
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) = ⊥ :=
    center_quotient_H_eq_bot hC
  have hS : IsSimpleGroup (commutator
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :=
    commutator_simple_imageClass hC hQ hmin hconn hHns
  have hW : WidthLe (imageClass hC) 2 := widthLe_imageClass_two hC (widthLe_three_of_config hQ)
  have hns : ¬ Group.IsSolvable
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
    not_isSolvable_quotient_solvableRadical hHns
  exact CFSG.Fischer.Classification.width_two_fischer_pair_is_S5 hP hZ hS hW hns

theorem imageClass_S5'
    (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (hmin : SmallerTwoStar (Nat.card G)) (hconn : ¬ Disconnected (imageClass hC))
    (htri : IsTriangle D u w v) (hu : u ∈ hC.alpha) (hv : v ∈ DalphaStar D hC.alpha)
    {X : Subgroup G} {R : Subgroup X} [R.Normal] (hR : Group.IsSolvable R)
    (hKX : thirdK D z ≤ X) (hPX : O4PairData (X ⧸ R) (Omega D X R)) :
    ∃ e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
        Equiv.Perm (Fin 5),
      e '' imageClass hC = transpositions :=
  imageClass_S5 hC hQ hmin hconn
    (not_isSolvable_Halpha_of_config hC hQ htri hu hv hR hKX hPX)

end CFSG.OddTranspositions
