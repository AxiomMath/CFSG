module

public import CFSG.OddTranspositions.AscTheoremTwo
public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.Timmesfeld.Closure.MinCex

import CFSG.OddTranspositions.PartThree.EightEight.Components
import CFSG.OddTranspositions.PartThree.EightEight.Triangles
import CFSG.OddTranspositions.PartThree.Nine.ThreeSplit
import CFSG.OddTranspositions.SevenLocalSecondConverse
import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Bridge.Asc72Lift
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.OddTranspositions.BlockAction2
import CFSG.OddTranspositions.CommutatorSize
import CFSG.OddTranspositions.SixSevenLocalStep
import CFSG.OddTranspositions.WidthOne

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem reach_DstarH_iff (hC : HypothesisC D) {x y : Halpha D hC.alpha} :
    Reach (DstarH hC) x y ↔ Reach (DalphaStar D hC.alpha) (x : G) (y : G) := by
  change Reach (((↑) : Halpha D hC.alpha → G) ⁻¹' DalphaStar D hC.alpha) x y ↔
    Reach (DalphaStar D hC.alpha) (x : G) (y : G)
  exact CFSG.Timmesfeld.Bridge.OddLocal.reach_preimage_iff
    (fun x hx => Subgroup.subset_closure hx)

theorem isTriangle_DstarH (hC : HypothesisC D) {u w v : G}
    (hu : u ∈ DalphaStar D hC.alpha) (hw : w ∈ DalphaStar D hC.alpha)
    (hv : v ∈ DalphaStar D hC.alpha) (ht : IsTriangle D u w v) :
    IsTriangle (DstarH hC) ⟨u, Subgroup.subset_closure hu⟩
      ⟨w, Subgroup.subset_closure hw⟩ ⟨v, Subgroup.subset_closure hv⟩ := by
  have hcomm : ∀ a b : Halpha D hC.alpha, Commute a b ↔ Commute (a : G) (b : G) :=
    fun a b => ⟨fun h => congrArg Subtype.val h.eq,
      fun h => (commute_iff_eq a b).mpr (Subtype.ext h.eq)⟩
  refine ⟨(mem_DstarH_iff hC).mpr hu, (mem_DstarH_iff hC).mpr hv,
    (mem_DstarH_iff hC).mpr hw, ?_, ?_, ?_, ?_⟩
  · intro h
    exact ht.2.2.2.1 (congrArg Subtype.val h)
  · exact (hcomm _ _).mpr ht.2.2.2.2.1
  · intro h
    exact ht.2.2.2.2.2.1 ((hcomm _ _).mp h)
  · intro h
    exact ht.2.2.2.2.2.2 ((hcomm _ _).mp h)

theorem orderOf_mul_eq_four_of_not_reach_DalphaStar (h86 : Lemma8_6) (hC : HypothesisC D)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {u w v : G} (hu : u ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hv : v ∈ DalphaStar D hC.alpha)
    (ht : IsTriangle D u w v) (hnot : ¬ Reach (DalphaStar D hC.alpha) u w) :
    orderOf (u * v * w) = 4 := by
  let H := Halpha D hC.alpha
  let uH : H := ⟨u, Subgroup.subset_closure hu⟩
  let wH : H := ⟨w, Subgroup.subset_closure hw⟩
  let vH : H := ⟨v, Subgroup.subset_closure hv⟩
  have htri : IsTriangle (DstarH hC) uH wH vH := isTriangle_DstarH hC hu hw hv ht
  have hnotH : ¬ Reach (DstarH hC) uH wH := fun h => hnot ((reach_DstarH_iff hC).mp h)
  have h4 := orderOf_mul_eq_four_of_not_reach h86 (PartThree.Nine.setup_DstarH hC) hne htri hnotH
  rwa [← Subgroup.orderOf_coe (uH * vH * wH)] at h4

theorem exists_isThirdKind_of_reach (h2 : AschbacherTheoremTwo) (h86 : Lemma8_6)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (h3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) (hO4 : ¬ O4PairData G D)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2) :
    ∃ x w y : G, IsTriangle D x w y ∧ IsThirdKind x w y ∧ x ∈ DalphaStar D hC.alpha ∧
      w ∈ DalphaStar D hC.alpha ∧ y ∈ DalphaStar D hC.alpha ∧
      Reach (DalphaStar D hC.alpha) x w := by
  by_contra hcon
  have hno : ∀ x w y : G, ¬ (IsTriangle D x w y ∧ IsThirdKind x w y ∧
      x ∈ DalphaStar D hC.alpha ∧ w ∈ DalphaStar D hC.alpha ∧
      y ∈ DalphaStar D hC.alpha ∧ Reach (DalphaStar D hC.alpha) x w) := by
    intro x w y h
    exact hcon ⟨x, w, y, h⟩
  have hAll : ∀ x ∈ DalphaStar D hC.alpha, ∀ y ∈ DalphaStar D hC.alpha,
      ∀ t ∈ DalphaStar D hC.alpha, IsTriangle D x y t → orderOf (x * t * y) = 4 := by
    intro x hx y hy t ht htri
    rcases IsTriangle.orderOf_cases hC.setup.oddT hC.setup.normal htri with hodd | h4 | hthird
    · exact absurd hodd.1 (not_odd_orderOf_of_derivedSeries_ne hC hne hx ht htri)
    · exact h4
    · by_cases hreach : Reach (DalphaStar D hC.alpha) x y
      · exact absurd ⟨htri, hthird, hx, hy, ht, hreach⟩ (hno x y t)
      · exact orderOf_mul_eq_four_of_not_reach_DalphaStar h86 hC hne hx hy ht htri hreach
  have hL : LocalSecond D := localSecond_of_DalphaStar_triangles hC hAll
  rcases h2 G D hC.setup hC hL hrad with h3' | hO4'
  · exact h3 h3'
  · exact hO4 hO4'

end CFSG.OddTranspositions.PartThree.EightEight

end
