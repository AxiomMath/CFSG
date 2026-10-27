module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalNormalizerOrbit

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem localNormalizer_point_pair_odd_core_factorization
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (Y : Subgroup G) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (beta : numeratorRightOrbit H Y (rightCosetMk H 1))
    (hbeta : beta.val ≠ rightCosetMk H 1) :
    ((H ⊓ Y : Subgroup G) : Set G) =
      (Y ⊓ Subgroup.centralizer ({z} : Set G) : Set G) *
        (Y ⊓ pairOddCore H beta.val : Subgroup G) := by
  let zY : Y := ⟨z, hzY⟩
  let e := localNormalizerCosetOrbitEquiv H Y
  let betaY := e.symm beta
  have hinclusion : subgroupRightCosetInclusion H Y betaY = beta.val :=
    congrArg Subtype.val (e.apply_symm_apply beta)
  have hbetaY : betaY ≠ rightCosetMk (H.subgroupOf Y) 1 := by
    intro heq
    have hbase := hinclusion
    rw [heq, subgroupRightCosetInclusion_mk, Subgroup.coe_one] at hbase
    exact hbeta hbase.symm
  have hlocal := (involution_point_subgroup_inheritance h Y hzY hescape).1
  obtain ⟨tY, htY⟩ := localPointHull_pair_flip_nonempty hlocal betaY hbetaY
  have htG : (tY : G) ∈ rightPairFlipFiber H z beta.val := by
    have hh := subgroup_flip_mem_ambient hzY htY
    rwa [hinclusion] at hh
  have htransversal := ((involution_point_uniform_pair_flips hlocal betaY hbetaY).2.2
    tY htY).2
  have hproducts := pair_inverted_set_eq_products h S hzS hzcenter hbeta htG
  have hJH : pairOddCore H beta.val ≤ H :=
    (Subgroup.map_subtype_le _).trans (pairPointStabilizer_le_point H beta.val)
  ext g
  constructor
  · rintro ⟨hgH, hgY⟩
    let gY : Y := ⟨g, hgY⟩
    obtain ⟨x, hxcoset, _⟩ := htransversal (⟨gY, hgH⟩ : H.subgroupOf Y)
    have hxY : ((x.val : Y) : G) ∈ Y := x.val.property
    have hxJ : ((x.val : Y) : G) ∈ pairOddCore H beta.val := by
      obtain ⟨rY, hrY, hprod⟩ := x.property
      have hrG : (rY : G) ∈ rightPairFlipFiber H z beta.val := by
        have hh := subgroup_flip_mem_ambient hzY hrY
        rwa [hinclusion] at hh
      have hxprod : ((x.val : Y) : G) ∈ rightPairFlipProducts H z beta.val (tY : G) :=
        ⟨(rY : G), hrG, congrArg Subtype.val hprod⟩
      exact (hproducts.symm ▸ hxprod).1
    have hxg : x.val * gY⁻¹ ∈ Subgroup.centralizer ({zY} : Set Y) :=
      (mem_rightCoset_iff
        (s := (Subgroup.centralizer ({zY} : Set Y) : Set Y)) gY).mp hxcoset
    have hginv : gY * x.val⁻¹ ∈ Subgroup.centralizer ({zY} : Set Y) := by
      simpa only [mul_inv_rev, inv_inv] using
        (Subgroup.centralizer ({zY} : Set Y)).inv_mem hxg
    have hcG : g * ((x.val : Y) : G)⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hginv))
    exact Set.mem_mul.mpr ⟨g * ((x.val : Y) : G)⁻¹,
      ⟨Y.mul_mem hgY (Y.inv_mem hxY), hcG⟩, ((x.val : Y) : G), ⟨hxY, hxJ⟩,
      by group⟩
  · intro hg
    obtain ⟨c, hc, t, ht, rfl⟩ := Set.mem_mul.mp hg
    exact ⟨H.mul_mem (point_centralizer_le h hc.2) (hJH ht.2),
      Y.mul_mem hc.1 ht.1⟩

theorem localNormalizer_point_class_eq_pair_odd_core_class
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (Y : Subgroup G) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (beta : numeratorRightOrbit H Y (rightCosetMk H 1))
    (hbeta : beta.val ≠ rightCosetMk H 1) :
    conjugacyWithin (H ⊓ Y) z = conjugacyWithin (Y ⊓ pairOddCore H beta.val) z := by
  have hfactor := localNormalizer_point_pair_odd_core_factorization h S hzS hzcenter
    Y hzY hescape beta hbeta
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    have hg : (g : G) ∈
        (Y ⊓ Subgroup.centralizer ({z} : Set G) : Set G) *
          (Y ⊓ pairOddCore H beta.val : Subgroup G) := by
      rw [← hfactor]
      exact g.property
    obtain ⟨c, hc, t, ht, hct⟩ := Set.mem_mul.mp hg
    have hcfix : c⁻¹ * z * c = z := by
      have hh := Subgroup.mem_centralizer_singleton_iff.mp hc.2
      rw [mul_assoc, ← hh, inv_mul_cancel_left]
    refine ⟨⟨t, ht⟩, ?_⟩
    change t⁻¹ * z * t = (g : G)⁻¹ * z * (g : G)
    rw [← hct, mul_inv_rev]
    calc
      t⁻¹ * z * t = t⁻¹ * (c⁻¹ * z * c) * t := by rw [hcfix]
      _ = t⁻¹ * c⁻¹ * z * (c * t) := by group
  · rintro ⟨t, rfl⟩
    have hJH : pairOddCore H beta.val ≤ H :=
      (Subgroup.map_subtype_le _).trans (pairPointStabilizer_le_point H beta.val)
    exact ⟨⟨t.val, hJH t.property.2, t.property.1⟩, rfl⟩

end CFSG.ShultStronglyClosedTI
