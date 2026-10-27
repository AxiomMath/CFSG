module

public import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.OddTranspositions.SixNineUnconditional

import CFSG.OddTranspositions.BlockGraph
import CFSG.OddTranspositions.PartThree.Eleven.OneOne.ConjShared
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.OddTranspositions

variable {G : Type*} [Group G]

theorem blockClass_eq_of_mem_blockClass {α β : Set G} (hβ : β ∈ blockClass α) :
    blockClass β = blockClass α := by
  refine Set.Subset.antisymm (fun γ hγ => ?_)
    (fun γ hγ => mem_blockClass_of_mem_blockClass hβ hγ)
  exact mem_blockClass_of_mem_blockClass (mem_blockClass_comm.mpr hβ) hγ

theorem FaithfulOnBlocks.of_mem_blockClass {α β : Set G} (hF : FaithfulOnBlocks α)
    (hβ : β ∈ blockClass α) : FaithfulOnBlocks β := by
  intro x hx
  exact hF x (fun γ hγ => hx γ (by rwa [← blockClass_eq_of_mem_blockClass hβ] at hγ))

end CFSG.OddTranspositions

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem not_isSolvable_Halpha_conj (hC : HypothesisC D) (g : G)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) :
    ¬ Group.IsSolvable (Halpha D (hC.conj g).alpha) := by
  intro hsol
  exact hns (Group.isSolvable_of_surjective
    (f := ((conjEquiv hC g).symm : Halpha D (hC.conj g).alpha →*
      Halpha D hC.alpha)) (conjEquiv hC g).symm.surjective)

omit [Finite G] in
theorem derivedSeries_Halpha_conj_ne (hC : HypothesisC D) (g : G)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2) :
    derivedSeries (Halpha D (hC.conj g).alpha) 1 ≠
      derivedSeries (Halpha D (hC.conj g).alpha) 2 := by
  intro h
  have h1 := map_derivedSeries_eq (f := ((conjEquiv hC g).symm :
    Halpha D (hC.conj g).alpha →* Halpha D hC.alpha))
    (conjEquiv hC g).symm.surjective 1
  have h2 := map_derivedSeries_eq (f := ((conjEquiv hC g).symm :
    Halpha D (hC.conj g).alpha →* Halpha D hC.alpha))
    (conjEquiv hC g).symm.surjective 2
  exact hne (by rw [← h1, ← h2, h])

theorem derivedSeries_quotient_Halpha_conj_ne (hC : HypothesisC D) (g : G)
    (hne : derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 1 ≠
      derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 2) :
    derivedSeries
        (Halpha D (hC.conj g).alpha ⧸ CFSG.solvableRadical (Halpha D (hC.conj g).alpha)) 1 ≠
      derivedSeries
        (Halpha D (hC.conj g).alpha ⧸ CFSG.solvableRadical (Halpha D (hC.conj g).alpha)) 2 := by
  intro h
  let e := QuotientGroup.congr (CFSG.solvableRadical (Halpha D hC.alpha))
    (CFSG.solvableRadical (Halpha D (hC.conj g).alpha)) (conjEquiv hC g)
    (conjRadical_map hC g)
  have h1 := map_derivedSeries_eq (f := e.symm.toMonoidHom) e.symm.surjective 1
  have h2 := map_derivedSeries_eq (f := e.symm.toMonoidHom) e.symm.surjective 2
  exact hne (by rw [← h1, ← h2, h])

omit [Finite G] in
theorem faithfulOnBlocks_conj_alpha (hC : HypothesisC D) (g : G)
    (hF : FaithfulOnBlocks hC.alpha) : FaithfulOnBlocks (hC.conj g).alpha := by
  refine FaithfulOnBlocks.of_mem_blockClass hF ?_
  rw [hC.conj_alpha]
  exact mem_blockClass_iff.mpr ⟨g, rfl⟩

end CFSG.OddTranspositions.PartThree
