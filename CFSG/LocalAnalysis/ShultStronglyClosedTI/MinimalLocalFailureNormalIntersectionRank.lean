module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNormalIntersectionMoving
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowEvenRank
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowEvenProduct

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem normalIntersection_deficient_sylow_hull_rank
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (C : Subgroup G) (hCB : C ≤ pairPointStabilizer H beta)
    (hBnormalizes : pairPointStabilizer H beta ≤ Subgroup.normalizer (C : Set G))
    (p : ℕ) (hp : p.Prime) (hpm : p ∣ Nat.card (conjugacyWithin H z))
    (Q : Sylow p (C ⊓ triplePointStabilizer H z beta : Subgroup G))
    (hzQ : z ∈ Subgroup.normalizer
      (((Q : Subgroup (C ⊓ triplePointStabilizer H z beta : Subgroup G)).map
        (C ⊓ triplePointStabilizer H z beta).subtype : Subgroup G) : Set G))
    (hUne : ((Q : Subgroup (C ⊓ triplePointStabilizer H z beta : Subgroup G)).map
      (C ⊓ triplePointStabilizer H z beta).subtype : Subgroup G) ≠ ⊥)
    (hdeficient : ¬ ∃ R : Sylow p C,
      (R : Subgroup C).map C.subtype =
        (Q : Subgroup (C ⊓ triplePointStabilizer H z beta : Subgroup G)).map
          (C ⊓ triplePointStabilizer H z beta).subtype) :
    let U := (Q : Subgroup (C ⊓ triplePointStabilizer H z beta : Subgroup G)).map
      (C ⊓ triplePointStabilizer H z beta).subtype
    let Y := Subgroup.normalizer (U : Set G)
    2 ≤ CFSG.Open.pRank 2 (Subgroup.closure (conjugacyWithin Y z)) := by
  let E := triplePointStabilizer H z beta
  let U := (Q : Subgroup (C ⊓ E : Subgroup G)).map (C ⊓ E).subtype
  let Y := Subgroup.normalizer (U : Set G)
  let L := Subgroup.closure (conjugacyWithin Y z)
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨A, hUA, hzA, _hinter, _T, _hWT, x, _hxT, _hxC, hxW, hxY,
    _hxE, hxbase, hxbeta, hxmove⟩ := normalIntersection_deficient_sylow_moving_element
      h.local_datum S hzS hzcenter beta hbeta C hCB hBnormalizes p hp Q hzQ hdeficient
  let W := (A : Subgroup E).map E.subtype
  have hWne : W ≠ ⊥ := by
    intro hbot
    exact hUne (le_bot_iff.mp (hbot ▸ hUA))
  have hxH : x ∈ H := (point_right_base_fixed_iff H x).mp hxbase
  have heven := noncentralSylow_moving_conjugate_even_product
    h hcomm beta hbeta p hp hpm A hzA hWne x hxH hxW hxbeta hxmove
  have hzL : z ∈ L := Subgroup.subset_closure ⟨1, by simp⟩
  have hsL : rightConjugateElem z x ∈ L := Subgroup.subset_closure ⟨⟨x, hxY⟩, rfl⟩
  let zL : L := ⟨z, hzL⟩
  let sL : L := ⟨rightConjugateElem z x, hsL⟩
  have hzorder : orderOf zL = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact h.local_datum.distinguished_order
  have hsorder : orderOf sL = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact order_two_of_mem_pointClass h.local_datum.distinguished_order ⟨x, rfl⟩
  have hevenL : Even (orderOf (zL * sL)) := by
    rw [← Subgroup.orderOf_coe]
    exact heven
  have hrank : 2 ≤ CFSG.Open.twoRank L :=
    noncentralSylow_two_rank_of_even_involution_product hzorder hsorder hevenL
  rw [CFSG.Open.twoRank, ← pRank_subgroup_eq_internal_top 2 (by decide) L] at hrank
  exact hrank

end CFSG.ShultStronglyClosedTI
