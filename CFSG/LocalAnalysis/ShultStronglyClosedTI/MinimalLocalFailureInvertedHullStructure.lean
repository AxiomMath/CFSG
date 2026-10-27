module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureInvertedHullData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureInvertedHullOddCore

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki CFSG.ProperTwoGeneratedCore
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem invertedHull_internal_embedding_transport (A H : Subgroup G) (zA : A)
    (hstrong : fusionStronglyEmbedded
      ((H.subgroupOf A).subgroupOf (involutionPointHull zA))) :
    fusionStronglyEmbedded (H.subgroupOf ((involutionPointHull zA).map A.subtype)) := by
  let LA := involutionPointHull zA
  let L := LA.map A.subtype
  let e : LA ≃* L := LA.equivMapOfInjective A.subtype Subtype.val_injective
  have he : ∀ a : LA, (e a : G) = ((a : A) : G) := fun _ => rfl
  have hmap : ((H.subgroupOf A).subgroupOf LA).map e.toMonoidHom = H.subgroupOf L := by
    ext l
    constructor
    · rintro ⟨a, ha, rfl⟩
      change (e a : G) ∈ H
      rw [he a]
      exact ha
    · intro hl
      refine ⟨e.symm l, ?_, e.apply_symm_apply l⟩
      change ((e.symm l : A) : G) ∈ H
      rw [← he (e.symm l), e.apply_symm_apply]
      exact hl
  have ht := hstrong.map_mulEquiv e
  rw [hmap] at ht
  exact ht

theorem invertedHull_strong_embedding
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (P : Subgroup G) (hPodd : Odd (Nat.card P))
    (hI : ∃ x ∈ minimalLocalFailureInvertedSet P z, x ≠ 1)
    (hescape : ¬ Subgroup.centralizer (minimalLocalFailureInvertedSet P z) ≤ H) :
    fusionStronglyEmbedded (H.subgroupOf (minimalLocalFailureInvertedHull P z)) := by
  let A := minimalLocalFailureInvertedOvergroup P z
  have hzA : z ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  let zA : A := ⟨z, hzA⟩
  have hAproper := invertedHull_overgroup_proper h P hPodd hI
  have hAescape : ¬ A ≤ H := fun hAH => hescape (le_sup_left.trans hAH)
  obtain ⟨hlocal, hcentral⟩ :=
    LocalCriterionSubgroupSylow.involution_point_subgroup_inheritance
      h.local_datum A hzA hAescape
  have hcard : Nat.card A < Nat.card G := by
    simpa only [Subgroup.card_top] using
      Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hAproper)
  have hstrong := h.smaller A hcard (H.subgroupOf A) zA hlocal
    (hcentral h.central_sylow)
  exact invertedHull_internal_embedding_transport A H zA hstrong

omit [Finite G] in
theorem invertedHull_internal_kernel_image (P : Subgroup G) (z : G) :
    let M := Subgroup.centralizer (minimalLocalFailureInvertedSet P z)
    let A := minimalLocalFailureInvertedOvergroup P z
    let zA : A := ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩
    let LA := involutionPointHull zA
    (LA ⊓ M.subgroupOf A).map A.subtype = minimalLocalFailureInvertedHull P z ⊓ M := by
  dsimp only
  rw [Subgroup.map_inf _ _ _ Subtype.val_injective]
  have hle : Subgroup.centralizer (minimalLocalFailureInvertedSet P z) ≤
      minimalLocalFailureInvertedOvergroup P z := le_sup_left
  rw [Subgroup.map_subgroupOf_eq_of_le hle]
  rfl

omit [Finite G] in
theorem invertedHull_distinguished_mem (P : Subgroup G) (z : G) :
    z ∈ minimalLocalFailureInvertedHull P z := by
  let A := minimalLocalFailureInvertedOvergroup P z
  let zA : A := ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩
  exact Subgroup.mem_map_of_mem A.subtype (localPointHull_distinguished_mem zA)

theorem invertedHull_odd_core_structure
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (P : Subgroup G) (hPodd : Odd (Nat.card P))
    (hI : ∃ x ∈ minimalLocalFailureInvertedSet P z, x ≠ 1)
    (hescape : ¬ Subgroup.centralizer (minimalLocalFailureInvertedSet P z) ≤ H) :
    let M := Subgroup.centralizer (minimalLocalFailureInvertedSet P z)
    let L := minimalLocalFailureInvertedHull P z
    let V := L ⊓ M
    (V.subgroupOf L).Normal ∧ Odd (Nat.card V) ∧ V.relIndex L = 2 ∧
      V = (oddCore L).map L.subtype ∧ L = V ⊔ Subgroup.zpowers z ∧
      (L : Set G) = (V : Set G) * (Subgroup.zpowers z : Set G) ∧
      Group.IsSolvable L := by
  let M := Subgroup.centralizer (minimalLocalFailureInvertedSet P z)
  let A := minimalLocalFailureInvertedOvergroup P z
  let MA := M.subgroupOf A
  let : MA.Normal := invertedHull_centralizer_normal P z h.local_datum.distinguished_order
  have hzA : z ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  let zA : A := ⟨z, hzA⟩
  let LA := involutionPointHull zA
  let VA := LA ⊓ MA
  let L := minimalLocalFailureInvertedHull P z
  let V := L ⊓ M
  have hAproper := invertedHull_overgroup_proper h P hPodd hI
  have hAescape : ¬ A ≤ H := fun hAH => hescape (le_sup_left.trans hAH)
  have hindex := invertedHull_centralizer_index_two P hPodd z
    h.local_datum.distinguished_order hI
  have hzMA : zA ∉ MA := invertedHull_involution_not_mem_centralizer P hPodd z hI
  obtain ⟨hVAnormal, hVAodd, hVAindex, hLAsup, hLAproduct, _⟩ :=
    minimalLocalFailure_smaller_index_two_odd_kernel h A hAproper hzA hAescape MA hindex hzMA
  let : VA.Normal := hVAnormal
  have himage : VA.map A.subtype = V := invertedHull_internal_kernel_image P z
  let e : LA ≃* L := LA.equivMapOfInjective A.subtype Subtype.val_injective
  have he : ∀ a : LA, (e a : G) = ((a : A) : G) := fun _ => rfl
  have hkernel : (VA.subgroupOf LA).map e.toMonoidHom = V.subgroupOf L := by
    ext l
    constructor
    · rintro ⟨a, ha, rfl⟩
      change (e a : G) ∈ V
      rw [he a, ← himage]
      exact Subgroup.mem_map_of_mem A.subtype ha
    · intro hl
      refine ⟨e.symm l, ?_, e.apply_symm_apply l⟩
      have hl' : (l : G) ∈ V := hl
      have hmem : (e (e.symm l) : G) ∈ V := by
        simpa only [e.apply_symm_apply] using hl'
      rw [he (e.symm l), ← himage] at hmem
      change (e.symm l : A) ∈ VA
      exact (Subgroup.mem_map_iff_mem (f := A.subtype) Subtype.val_injective).mp hmem
  have hVnormal : (V.subgroupOf L).Normal := by
    rw [← hkernel]
    exact (inferInstance : (VA.subgroupOf LA).Normal).map e.toMonoidHom e.surjective
  let : (V.subgroupOf L).Normal := hVnormal
  have hVodd : Odd (Nat.card V) := by
    rw [← himage, Subgroup.card_map_of_injective Subtype.val_injective]
    exact hVAodd
  have hVindex : V.relIndex L = 2 := by
    have ht := Subgroup.relIndex_map_map_of_injective (f := A.subtype) VA LA
      Subtype.val_injective
    rw [himage] at ht
    exact ht.trans hVAindex
  have hVL : V ≤ L := inf_le_left
  have hinternalOdd : Odd (Nat.card (V.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv]
    exact hVodd
  have hcore : V = (oddCore L).map L.subtype := by
    have hi := invertedHull_odd_index_two_eq_oddCore (V.subgroupOf L) hinternalOdd hVindex
    rw [← hi, Subgroup.map_subgroupOf_eq_of_le hVL]
  have hLsup : L = V ⊔ Subgroup.zpowers z := by
    have hi := congrArg (Subgroup.map A.subtype) hLAsup
    rw [Subgroup.map_sup, himage, MonoidHom.map_zpowers] at hi
    exact hi
  have hproduct : (L : Set G) = (V : Set G) * (Subgroup.zpowers z : Set G) := by
    ext l
    constructor
    · intro hl
      obtain ⟨a, ha, rfl⟩ := hl
      have hp : a ∈ (LA : Set A) := ha
      rw [hLAproduct] at hp
      obtain ⟨v, hv, t, ht, hvt⟩ := hp
      refine Set.mem_mul.mpr ⟨v, ?_, t, ?_, congrArg Subtype.val hvt⟩
      · rw [← himage]
        exact Subgroup.mem_map_of_mem A.subtype hv
      · have hm := Subgroup.mem_map_of_mem A.subtype ht
        rw [MonoidHom.map_zpowers] at hm
        exact hm
    · rintro ⟨v, hv, t, ht, rfl⟩
      have htL : t ∈ L := by rw [hLsup]; exact Subgroup.mem_sup_right ht
      exact L.mul_mem (hVL hv) htL
  exact ⟨hVnormal, hVodd, hVindex, hcore, hLsup, hproduct,
    invertedHull_odd_index_two_solvable (V.subgroupOf L) hinternalOdd hVindex⟩

theorem invertedHull_point_intersection_product
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (P : Subgroup G)
    (hescape : ¬ Subgroup.centralizer (minimalLocalFailureInvertedSet P z) ≤ H) :
    (H ⊓ minimalLocalFailureInvertedOvergroup P z : Set G) =
      (minimalLocalFailureInvertedOvergroup P z ⊓ Subgroup.centralizer ({z} : Set G) : Set G) *
        (H ⊓ minimalLocalFailureInvertedHull P z : Set G) := by
  let A := minimalLocalFailureInvertedOvergroup P z
  have hzA : z ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  let zA : A := ⟨z, hzA⟩
  let LA := involutionPointHull zA
  let L := minimalLocalFailureInvertedHull P z
  have hAescape : ¬ A ≤ H := fun hAH => hescape (le_sup_left.trans hAH)
  obtain ⟨hlocal, _⟩ :=
    LocalCriterionSubgroupSylow.involution_point_subgroup_inheritance
      h.local_datum A hzA hAescape
  have hfactor := localPointHull_point_eq_centralizer_mul hlocal
  ext a
  constructor
  · intro ha
    let aA : A := ⟨a, ha.2⟩
    have hm : aA ∈ (H.subgroupOf A : Set A) := ha.1
    rw [hfactor] at hm
    obtain ⟨c, hc, l, hl, hcl⟩ := hm
    refine Set.mem_mul.mpr ⟨c, ⟨c.property, ?_⟩, l,
      ⟨hl.1, Subgroup.mem_map_of_mem A.subtype hl.2⟩, congrArg Subtype.val hcl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))
  · rintro ⟨c, hc, l, hl, rfl⟩
    have hcH : c ∈ H := by
      have hcA : (⟨c, hc.1⟩ : A) ∈ Subgroup.centralizer ({zA} : Set A) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hc.2))
      exact point_centralizer_le hlocal hcA
    exact ⟨H.mul_mem hcH hl.1, A.mul_mem hc.1 (Subgroup.map_subtype_le LA hl.2)⟩

end CFSG.ShultStronglyClosedTI
