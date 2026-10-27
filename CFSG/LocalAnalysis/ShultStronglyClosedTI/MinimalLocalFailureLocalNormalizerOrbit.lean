module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorRightOrbit
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalPointHullClass

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

universe u

variable {G : Type u} [Group G]

theorem localNormalizer_subgroup_coset_mem_orbit (H Y : Subgroup G)
    (omega : rightCosetSpace (H.subgroupOf Y)) :
    subgroupRightCosetInclusion H Y omega ∈
      numeratorRightOrbit H Y (rightCosetMk H 1) := by
  refine Quotient.inductionOn omega ?_
  intro y
  exact ⟨(y : G), y.property, by
    simp only [pointRightCosetMul_eq_translate, rightCosetTranslate_mk, one_mul]
    rfl⟩

@[expose] def localNormalizerCosetOrbitEquiv (H Y : Subgroup G) :
    rightCosetSpace (H.subgroupOf Y) ≃
      numeratorRightOrbit H Y (rightCosetMk H 1) :=
  Equiv.ofBijective
    (fun omega => ⟨subgroupRightCosetInclusion H Y omega,
      localNormalizer_subgroup_coset_mem_orbit H Y omega⟩)
    ⟨by
      intro a b hab
      exact subgroupRightCosetInclusion_injective H Y (congrArg Subtype.val hab), by
      rintro ⟨omega, y, hy, hyo⟩
      refine ⟨rightCosetMk (H.subgroupOf Y) (⟨y, hy⟩ : Y), ?_⟩
      apply Subtype.ext
      simpa only [subgroupRightCosetInclusion_mk, pointRightCosetMul_eq_translate,
        rightCosetTranslate_mk, one_mul]
        using hyo⟩

theorem localNormalizerCosetOrbitEquiv_apply (H Y : Subgroup G)
    (omega : rightCosetSpace (H.subgroupOf Y)) :
    (localNormalizerCosetOrbitEquiv H Y omega).val =
      subgroupRightCosetInclusion H Y omega := rfl

theorem localNormalizerCosetOrbitEquiv_translate (H Y : Subgroup G)
    (omega : rightCosetSpace (H.subgroupOf Y)) (y : Y) :
    (localNormalizerCosetOrbitEquiv H Y
      (rightCosetTranslate (H.subgroupOf Y) omega y)).val =
        pointRightCosetMul H (localNormalizerCosetOrbitEquiv H Y omega).val (y : G) := by
  rw [localNormalizerCosetOrbitEquiv_apply, localNormalizerCosetOrbitEquiv_apply,
    subgroupRightCosetInclusion_translate, pointRightCosetMul_eq_translate]

theorem localNormalizer_internal_hull_transitive_original_orbit
    [Finite G] (H Y : Subgroup G) (zY : Y)
    (hlocal : InvolutionPointLocalEmbedding (H.subgroupOf Y) zY) :
    ∀ a b : numeratorRightOrbit H Y (rightCosetMk H 1),
      ∃ l : involutionPointHull zY,
        pointRightCosetMul H a.val (((l : Y) : G)) = b.val := by
  intro a b
  let e := localNormalizerCosetOrbitEquiv H Y
  obtain ⟨l, hl⟩ := localPointHull_right_coset_transitive hlocal (e.symm a) (e.symm b)
  have ht := localNormalizerCosetOrbitEquiv_translate H Y (e.symm a) (l : Y)
  change (e (rightCosetTranslate (H.subgroupOf Y) (e.symm a) (l : Y))).val =
    pointRightCosetMul H (e (e.symm a)).val (((l : Y) : G)) at ht
  rw [hl, e.apply_symm_apply, e.apply_symm_apply] at ht
  exact ⟨l, ht.symm⟩

end CFSG.ShultStronglyClosedTI
