module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNormalIntersectionAlgebra
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowGrowth
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowQuotient

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

variable {G : Type*} [Group G] [Finite G]

theorem normalIntersection_deficient_sylow_moving_element
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (C : Subgroup G) (hCB : C ≤ pairPointStabilizer H beta)
    (hBnormalizes : pairPointStabilizer H beta ≤ Subgroup.normalizer (C : Set G))
    (p : ℕ) (hp : p.Prime)
    (Q : Sylow p (C ⊓ triplePointStabilizer H z beta : Subgroup G))
    (hzQ : z ∈ Subgroup.normalizer
      (((Q : Subgroup (C ⊓ triplePointStabilizer H z beta : Subgroup G)).map
        (C ⊓ triplePointStabilizer H z beta).subtype : Subgroup G) : Set G))
    (hdeficient : ¬ ∃ R : Sylow p C,
      (R : Subgroup C).map C.subtype =
        (Q : Subgroup (C ⊓ triplePointStabilizer H z beta : Subgroup G)).map
          (C ⊓ triplePointStabilizer H z beta).subtype) :
    let E := triplePointStabilizer H z beta
    let U := (Q : Subgroup (C ⊓ E : Subgroup G)).map (C ⊓ E).subtype
    ∃ A : Sylow p E,
      let W := (A : Subgroup E).map E.subtype
      U ≤ W ∧ z ∈ Subgroup.normalizer (W : Set G) ∧ W ⊓ C = U ∧
        ∃ T : Sylow p (C ⊔ E : Subgroup G),
          let TG := (T : Subgroup (C ⊔ E : Subgroup G)).map (C ⊔ E).subtype
          W < TG ∧ ∃ x : G, x ∈ TG ∧ x ∈ C ∧
            x ∈ Subgroup.normalizer (W : Set G) ∧
            x ∈ Subgroup.normalizer (U : Set G) ∧ x ∉ E ∧
            pointRightCosetMul H (rightCosetMk H 1) x = rightCosetMk H 1 ∧
            pointRightCosetMul H beta x = beta ∧
            pointRightCosetMul H (pointRightCosetMul H beta z) x ≠
              pointRightCosetMul H beta z := by
  let B := pairPointStabilizer H beta
  let E := triplePointStabilizer H z beta
  let U := (Q : Subgroup (C ⊓ E : Subgroup G)).map (C ⊓ E).subtype
  let D := C ⊔ E
  let CD := C.subgroupOf D
  have hUE : U ≤ E := (Subgroup.map_subtype_le _).trans inf_le_right
  have hDB : D ≤ B := sup_le hCB inf_le_left
  have hDnormalizes : D ≤ Subgroup.normalizer (C : Set G) :=
    hDB.trans hBnormalizes
  let _ : CD.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDnormalizes
  obtain ⟨_hUtriple, A, hUA, hzA, _hfixed⟩ := triple_invariant_subgroup_extends
    h S hzS hzcenter beta hbeta p hp U (hUE.trans inf_le_left)
      (Q.isPGroup'.map (C ⊓ E).subtype) hzQ
  let W := (A : Subgroup E).map E.subtype
  have hWE : W ≤ E := Subgroup.map_subtype_le _
  have hWD : W ≤ D := hWE.trans le_sup_right
  have hinter : W ⊓ C = U := normalIntersection_triple_sylow_intersection
    p hp C E (inf_le_left.trans hBnormalizes) Q A hUA
  have hnotfull := normalIntersection_join_sylow_deficiency
    p hp C E hDnormalizes Q A hUA hdeficient
  have hWp : IsPGroup p W := A.isPGroup'.map E.subtype
  have hWDp : IsPGroup p (W.subgroupOf D) := hWp.comap_subtype
  obtain ⟨T, hWTin⟩ := hWDp.exists_le_sylow
  let TG := (T : Subgroup D).map D.subtype
  have hWT : W ≤ TG := by
    have hmap := Subgroup.map_mono (f := D.subtype) hWTin
    rw [Subgroup.map_subgroupOf_eq_of_le hWD] at hmap
    exact hmap
  have hstrict : W < TG := lt_of_le_of_ne hWT (by
    intro heq
    exact hnotfull ⟨T, heq.symm⟩)
  let q := QuotientGroup.mk' CD
  have hsurj : Function.Surjective (q.domRestrict (E.subgroupOf D)) :=
    normalIntersection_join_quotient_surjective C E inferInstance
  have himages := noncentralSylow_containing_pgroup_image_eq p hp D E le_sup_right
    q hsurj A TG (T.isPGroup'.map D.subtype) hWT
  have hsubtypeT : TG.subgroupOf D = (T : Subgroup D) := by
    ext d
    exact Subgroup.mem_map_iff_mem D.subtype_injective
  rw [hsubtypeT] at himages
  have hWTinside : W.subgroupOf D < (T : Subgroup D) := by
    apply (Subgroup.map_subtype_lt_map_subtype).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hWD]
    exact hstrict
  obtain ⟨xD, hxT, hxker, hxN, hxW⟩ := noncentralSylow_kernel_normalizer_growth
    p hp (T : Subgroup D) (W.subgroupOf D) T.isPGroup' hWTinside q himages
  have hxG : (xD : G) ∈ TG := Subgroup.mem_map_of_mem D.subtype hxT
  have hxC : (xD : G) ∈ C := by
    have hxCD : xD ∈ CD := by
      rwa [QuotientGroup.ker_mk'] at hxker
    exact hxCD
  have hxNG : (xD : G) ∈ Subgroup.normalizer (W : Set G) := by
    have hh := Subgroup.le_normalizer_map D.subtype
      (Subgroup.mem_map_of_mem D.subtype hxN)
    rwa [Subgroup.map_subgroupOf_eq_of_le hWD] at hh
  have hxNU : (xD : G) ∈ Subgroup.normalizer (U : Set G) := by
    rw [← hinter]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hxNG, Subgroup.le_normalizer hxC⟩
  have hxnotE : (xD : G) ∉ E := by
    intro hxE
    have hTGinter : TG ⊓ E = W := noncentralSylow_containing_pgroup_intersection
      p E A TG (T.isPGroup'.map D.subtype) hWT
    have hxWG : (xD : G) ∈ W := by
      rw [← hTGinter]
      exact ⟨hxG, hxE⟩
    exact hxW hxWG
  have hxB : (xD : G) ∈ B := hCB hxC
  have hxbase : pointRightCosetMul H (rightCosetMk H 1) (xD : G) = rightCosetMk H 1 :=
    (mem_point_right_stabilizer_iff H _ _).mp hxB.1
  have hxbeta : pointRightCosetMul H beta (xD : G) = beta :=
    (mem_point_right_stabilizer_iff H _ _).mp hxB.2
  refine ⟨A, hUA, hzA, hinter, T, hstrict, xD, hxG, hxC, hxNG, hxNU,
    hxnotE, hxbase, hxbeta, ?_⟩
  intro hfix
  apply hxnotE
  refine ⟨hxB, ?_⟩
  apply (mem_point_right_stabilizer_iff H _ _).mpr
  simpa only [pointRightCosetMul_eq_translate] using hfix

end CFSG.ShultStronglyClosedTI
