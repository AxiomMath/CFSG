module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowEvenRank
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowEvenProduct
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowExtension
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowMoving

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem noncentralSylow_odd_core_normalizer_hull_rank
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hpm : p ∣ Nat.card (conjugacyWithin H z))
    (P : Sylow p ((CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
        ((CFSG.oddCore (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype).subtype : Subgroup G) : Set G))
    (hUne : ((P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype)).map
      ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype).subtype : Subgroup G) ≠ ⊥) :
    let E := triplePointStabilizer H z beta
    let V := (CFSG.oddCore E).map E.subtype
    let U := (P : Subgroup V).map V.subtype
    let M := Subgroup.normalizer (U : Set G)
    2 ≤ CFSG.Open.pRank 2 (Subgroup.closure (conjugacyWithin M z)) := by
  let E := triplePointStabilizer H z beta
  let V := (CFSG.oddCore E).map E.subtype
  let U := (P : Subgroup V).map V.subtype
  let M := Subgroup.normalizer (U : Set G)
  let L := Subgroup.closure (conjugacyWithin M z)
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨A, hUA, hzA, _hWV, hWJ⟩ := noncentralSylow_triple_extension
    h.local_datum S hzS hzcenter beta hbeta p hp P hzP
  let W := (A : Subgroup E).map E.subtype
  change W ⊓ pairOddCore H beta = U at hWJ
  have hWne : W ≠ ⊥ := by
    intro hbot
    exact hUne (le_bot_iff.mp (hbot ▸ hUA))
  obtain ⟨_T, _hWT, x, _hxT, hxJ, hxW, _hxE, hxbase, hxbeta, hxmove⟩ :=
    noncentralSylow_triple_normalizing_moving_element h beta hbeta p hp hpm A hzA
  have hxM : x ∈ M := by
    change x ∈ Subgroup.normalizer (U : Set G)
    rw [← hWJ]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hxW, Subgroup.le_normalizer hxJ⟩
  have hxH : x ∈ H := (point_right_base_fixed_iff H x).mp hxbase
  have heven := noncentralSylow_moving_conjugate_even_product
    h hcomm beta hbeta p hp hpm A hzA hWne x hxH hxW hxbeta hxmove
  have hzL : z ∈ L := Subgroup.subset_closure ⟨1, by simp⟩
  have hsL : rightConjugateElem z x ∈ L := Subgroup.subset_closure ⟨⟨x, hxM⟩, rfl⟩
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
