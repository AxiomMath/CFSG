module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerSylowObstruction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowGrowth
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowConsequences

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

variable {G : Type*} [Group G] [Finite G]

theorem noncentralSylow_triple_pair_quotient_surjective
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    let B := pairPointStabilizer H beta
    let E := triplePointStabilizer H z beta
    Function.Surjective ((QuotientGroup.mk' (CFSG.oddCore B)).domRestrict
      (E.subgroupOf B)) := by
  let B := pairPointStabilizer H beta
  let E := triplePointStabilizer H z beta
  let q := QuotientGroup.mk' (CFSG.oddCore B)
  change Function.Surjective (q.domRestrict (E.subgroupOf B))
  obtain ⟨t, ht⟩ := original_pair_flip_exists h beta hbeta
  intro a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore B) a
  have hb : (b : G) ∈ (pairPointStabilizer H beta : Set G) := b.property
  rw [pair_stabilizer_eq_odd_core_mul_triple h S hzS hzcenter hbeta ht] at hb
  obtain ⟨j, hj, e, he, hje⟩ := Set.mem_mul.mp hb
  obtain ⟨jB, hjB, hjval⟩ := Subgroup.mem_map.mp hj
  change (jB : G) = j at hjval
  let eB : E.subgroupOf B := ⟨⟨e, he.1⟩, he⟩
  have hprod : b = jB * (eB : B) := by
    apply Subtype.ext
    change (b : G) = (jB : G) * e
    rw [hjval]
    exact hje.symm
  have hjq : q jB = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [QuotientGroup.ker_mk']
    exact hjB
  refine ⟨eB, ?_⟩
  change q (eB : B) = q b
  rw [hprod, map_mul, hjq, one_mul]

theorem noncentralSylow_triple_normalizing_moving_element
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hpm : p ∣ Nat.card (conjugacyWithin H z))
    (A : Sylow p (triplePointStabilizer H z beta))
    (hzA : z ∈ Subgroup.normalizer
      (((A : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G)) :
    let W := (A : Subgroup (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype
    ∃ T : Sylow p (pairPointStabilizer H beta),
      let TG := (T : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype
      W < TG ∧ ∃ x : G, x ∈ TG ∧ x ∈ pairOddCore H beta ∧
        x ∈ Subgroup.normalizer (W : Set G) ∧ x ∉ triplePointStabilizer H z beta ∧
        pointRightCosetMul H (rightCosetMk H 1) x = rightCosetMk H 1 ∧
        pointRightCosetMul H beta x = beta ∧
        pointRightCosetMul H (pointRightCosetMul H beta z) x ≠ pointRightCosetMul H beta z := by
  let B := pairPointStabilizer H beta
  let E := triplePointStabilizer H z beta
  let W := (A : Subgroup E).map E.subtype
  have hWE : W ≤ E := Subgroup.map_subtype_le _
  have hWB : W ≤ B := hWE.trans inf_le_left
  have hWp : IsPGroup p W := A.isPGroup'.map E.subtype
  have hWBin : IsPGroup p (W.subgroupOf B) := hWp.comap_subtype
  obtain ⟨T, hWTin⟩ := hWBin.exists_le_sylow
  let TG := (T : Subgroup B).map B.subtype
  have hWT : W ≤ TG := by
    have hmap := Subgroup.map_mono (f := B.subtype) hWTin
    rw [Subgroup.map_subgroupOf_eq_of_le hWB] at hmap
    exact hmap
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hstats := minimalLocalFailureSylowFixedPoints h
  have hdoubly := hstats.2.2.1
  have hambient : ∀ R : Sylow p G, Nat.card (pointFixedSet H (R : Subgroup G)) = 2 :=
    fun R => (hstats.2.2.2 p hp hpm).1 R |>.1
  have hnotambient := (original_triple_sylow_full_fixed_count_and_sylow_obstructions
    h.local_datum S hzS hzcenter hdoubly beta hbeta p hp hambient A hzA).2.2.1
  have hTGfull : ∃ R : Sylow p G, (R : Subgroup G) = TG := by
    have hh := (hstats.2.2.2 p hp hpm).2 (rightCosetMk H 1) beta hbeta.symm T
    exact hh.1
  have hstrict : W < TG := lt_of_le_of_ne hWT (by
    intro heq
    obtain ⟨R, hR⟩ := hTGfull
    exact hnotambient ⟨R, hR.trans heq.symm⟩)
  let q := QuotientGroup.mk' (CFSG.oddCore B)
  have hsurj : Function.Surjective (q.domRestrict (E.subgroupOf B)) :=
    noncentralSylow_triple_pair_quotient_surjective h.local_datum S hzS hzcenter beta hbeta
  have himages := noncentralSylow_containing_pgroup_image_eq p hp B E inf_le_left
    q hsurj A TG (T.isPGroup'.map B.subtype) hWT
  have hsubtypeT : TG.subgroupOf B = (T : Subgroup B) := by
    ext b
    exact Subgroup.mem_map_iff_mem B.subtype_injective
  rw [hsubtypeT] at himages
  have hWTB : W.subgroupOf B < (T : Subgroup B) := by
    apply (Subgroup.map_subtype_lt_map_subtype).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hWB]
    exact hstrict
  obtain ⟨xB, hxT, hxker, hxN, hxW⟩ := noncentralSylow_kernel_normalizer_growth
    p hp (T : Subgroup B) (W.subgroupOf B) T.isPGroup' hWTB q himages
  have hxG : (xB : G) ∈ TG := Subgroup.mem_map_of_mem B.subtype hxT
  have hxJ : (xB : G) ∈ pairOddCore H beta := by
    have hxcore : xB ∈ CFSG.oddCore B := by
      rwa [QuotientGroup.ker_mk'] at hxker
    exact Subgroup.mem_map_of_mem B.subtype hxcore
  have hxNG : (xB : G) ∈ Subgroup.normalizer (W : Set G) := by
    have hh := Subgroup.le_normalizer_map B.subtype
      (Subgroup.mem_map_of_mem B.subtype hxN)
    rwa [Subgroup.map_subgroupOf_eq_of_le hWB] at hh
  have hxnotE : (xB : G) ∉ E := by
    intro hxE
    have hinter : TG ⊓ E = W := noncentralSylow_containing_pgroup_intersection p E A TG
      (T.isPGroup'.map B.subtype) hWT
    have hxWG : (xB : G) ∈ W := by
      rw [← hinter]
      exact ⟨hxG, hxE⟩
    exact hxW hxWG
  have hxbase : pointRightCosetMul H (rightCosetMk H 1) (xB : G) = rightCosetMk H 1 :=
    (mem_point_right_stabilizer_iff H _ _).mp xB.property.1
  have hxbeta : pointRightCosetMul H beta (xB : G) = beta :=
    (mem_point_right_stabilizer_iff H _ _).mp xB.property.2
  refine ⟨T, hstrict, xB, hxG, hxJ, hxNG, hxnotE, hxbase, hxbeta, ?_⟩
  intro hfix
  apply hxnotE
  refine ⟨xB.property, ?_⟩
  apply (mem_point_right_stabilizer_iff H _ _).mpr
  simpa only [pointRightCosetMul_eq_translate] using hfix

end CFSG.ShultStronglyClosedTI
