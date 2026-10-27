module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaClass
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairSwapAmbient
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalNormalizerAction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaConstruction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaImage

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap
open CFSG.ComponentClassification.TwoRankTransport

universe u v

variable {G : Type u} [Group G]

theorem strongly_embedded_full_point_class_image [Finite G]
    {F : Type v} [Group F] [Finite F] (f : F →* G) (hf : Function.Injective f)
    (A : Subgroup G) {z : F} (hzA : z ∈ A.comap f) (hz : IsInvolution z)
    (hstrong : CFSG.BenderSuzuki.IsStronglyEmbedded (A.comap f))
    (hclass : conjugacyWithin A (f z) ⊆ f.range) :
    f '' conjugacyWithin (A.comap f) z = conjugacyWithin A (f z) := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨⟨f a, a.property⟩, by simp only [map_mul, map_inv]⟩
  · intro hx
    obtain ⟨y, hy⟩ := hclass hx
    have hxA : x ∈ A := by
      obtain ⟨a, rfl⟩ := hx
      exact A.mul_mem (A.mul_mem (A.inv_mem a.property) hzA) a.property
    have hyA : y ∈ A.comap f := by
      change f y ∈ A
      rwa [hy]
    have hxi : IsInvolution x := by
      have hzi : IsInvolution (f z) := ⟨fun h => hz.ne_one (hf (by simpa using h)),
        by simpa only [map_pow, map_one] using congrArg f hz.sq_eq_one⟩
      obtain ⟨a, rfl⟩ := hx
      have ha2 := order_two_of_mem_pointClass
        (orderOf_eq_prime hzi.sq_eq_one hzi.ne_one)
        (show (a : G)⁻¹ * f z * a ∈ involutionPointClass (f z) from ⟨a, rfl⟩)
      exact ⟨(orderOf_eq_prime_iff.mp ha2).2, (orderOf_eq_prime_iff.mp ha2).1⟩
    have hyi : IsInvolution y := by
      refine ⟨?_, ?_⟩
      · intro h
        apply hxi.ne_one
        rw [← hy, h, map_one]
      · apply hf
        rw [map_pow, hy, hxi.sq_eq_one, map_one]
    obtain ⟨a, ha, hconj⟩ := hstrong.involutions_conjugate_in hzA hz hyA hyi
    exact ⟨y, ⟨⟨a, ha⟩, hconj⟩, hy⟩

theorem injective_odd_quotient_kernel [Finite G]
    {F : Type v} [Group F] [Finite F] (f : G →* F) (hf : Function.Injective f)
    (R : Subgroup F) [R.Normal] (hRodd : Odd (Nat.card R)) :
    Odd (Nat.card ((QuotientGroup.mk' R).comp f).ker) := by
  let q := QuotientGroup.mk' R
  let C := (q.comp f).ker
  let e : C →* R := (f.comp C.subtype).codRestrict R (by
    intro x
    exact (QuotientGroup.eq_one_iff (f x)).mp (MonoidHom.mem_ker.mp x.property))
  have hinj : Function.Injective e := by
    intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  exact hRodd.of_dvd_nat (Subgroup.card_dvd_of_injective e hinj)

theorem odd_kernel_image_structure [Finite G]
    {F : Type v} [Group F] [Finite F] (f : G →* F)
    (hkernel : Odd (Nat.card f.ker))
    (I U : Subgroup G) [I.Normal] (hUodd : Odd (Nat.card U))
    (hgen : I ⊔ U = ⊤) [IsElementaryAbelian 2 (I.map f)] :
    Group.IsSolvable G ∧
      (∀ S : Subgroup G, IsPGroup 2 S → IsElementaryAbelian 2 S) ∧
      (CFSG.oddCore G).map f ≤ U.map f := by
  let g := f.rangeRestrict
  have hgkernel : g.ker = f.ker := by
    ext x
    change (⟨f x, _⟩ : f.range) = 1 ↔ f x = 1
    exact Subtype.ext_iff
  have hgelem : IsElementaryAbelian 2 (I.map g) := by
    let e : I.map g →* I.map f :=
      (f.range.subtype.comp (I.map g).subtype).codRestrict _ (by
        rintro ⟨x, hx⟩
        obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.mp hx
        exact Subgroup.mem_map.mpr ⟨i, hi, rfl⟩)
    apply elementary_of_injective e
    intro x y h
    have hh : (x.val.val : F) = y.val.val :=
      congrArg (fun a : I.map f => (a : F)) h
    exact Subtype.ext (Subtype.ext hh)
  let : IsElementaryAbelian 2 (I.map g) := hgelem
  have hgodd : Odd (Nat.card g.ker) := hgkernel.symm ▸ hkernel
  have hsurj : Function.Surjective g := f.rangeRestrict_surjective
  have hsol := odd_kernel_elementary_image_solvable g hsurj hgodd I U hUodd hgen
  have htwo := odd_kernel_elementary_image_two_subgroup g hsurj hgodd I U hUodd hgen
  let : (I.map g).Normal := (inferInstance : I.Normal).map g hsurj
  let : ((CFSG.oddCore G).map g).Normal :=
    (inferInstance : (CFSG.oddCore G).Normal).map g hsurj
  have hgenimage : I.map g ⊔ U.map g = ⊤ := by
    rw [← Subgroup.map_sup, hgen, Subgroup.map_top, g.range_eq_top_of_surjective hsurj]
  have hUimageodd : Odd (Nat.card (U.map g)) :=
    hUodd.of_dvd_nat (Subgroup.card_map_dvd U g)
  have hRimageodd : Odd (Nat.card ((CFSG.oddCore G).map g)) :=
    (CFSG.ComponentClassification.OddCore.odd_card G).of_dvd_nat
      (Subgroup.card_map_dvd (CFSG.oddCore G) g)
  have hcore := normal_odd_le_odd_supplement (I.map g) (U.map g)
    ((CFSG.oddCore G).map g) hUimageodd hRimageodd hgenimage
  refine ⟨hsol, htwo, ?_⟩
  have heq : f.range.subtype.comp g = f := by ext x; rfl
  have hh := Subgroup.map_mono (f := f.range.subtype) hcore
  simpa only [Subgroup.map_map, heq] using hh

theorem local_theta_actual_structure [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (X : Subgroup G) (hXH : X ≤ H) (hXne : X ≠ ⊥)
    (hXz : rightConjugate X z = X)
    (hescape : ¬ Subgroup.normalizer (X : Set G) ≤ H)
    (hrank : 2 ≤ CFSG.Open.pRank 2
      (Subgroup.closure (conjugacyWithin (Subgroup.normalizer (X : Set G)) z)))
    (beta : numeratorRightOrbit H (Subgroup.normalizer (X : Set G)) (rightCosetMk H 1))
    (hbeta : beta.val ≠ rightCosetMk H 1) {p : ℕ} (hp : p.Prime) :
    let Y := Subgroup.normalizer (X : Set G)
    let zY : Y := ⟨z, invariant_subgroup_mem_normalizer hXz⟩
    let L := involutionPointHull zY
    let D := Y ⊓ pairPointStabilizer H beta.val
    let T := Y ⊓ pairOddCore H beta.val
    let U := T ⊔ minimalLocalFailurePairConfinementTheta p D
    let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
    let K := I ⊔ U
    let F := L ⊔ U.subgroupOf Y
    let f := Y.subtype.comp F.subtype
    Group.IsSolvable K ∧ TwoRankAtLeastTwo K ∧
      (∀ S : Subgroup K, IsPGroup 2 S → IsElementaryAbelian 2 S) ∧
      (∀ v : G, (v ∈ K ∧ IsInvolution v) ↔ v ∈ conjugacyWithin T z) ∧
      ∃ kF : K →* F, Function.Injective kF ∧ f.comp kF = K.subtype ∧
        Odd (Nat.card ((QuotientGroup.mk' (CFSG.oddCore F)).comp kF).ker) ∧
        IsElementaryAbelian 2 ((I.subgroupOf K).map
          ((QuotientGroup.mk' (CFSG.oddCore F)).comp kF)) ∧
        (CFSG.oddCore K).map ((QuotientGroup.mk' (CFSG.oddCore F)).comp kF) ≤
          (U.subgroupOf K).map ((QuotientGroup.mk' (CFSG.oddCore F)).comp kF) := by
  let Y := Subgroup.normalizer (X : Set G)
  have hzY : z ∈ Y := invariant_subgroup_mem_normalizer hXz
  let zY : Y := ⟨z, hzY⟩
  let L := involutionPointHull zY
  let D := Y ⊓ pairPointStabilizer H beta.val
  let T := Y ⊓ pairOddCore H beta.val
  let U := T ⊔ minimalLocalFailurePairConfinementTheta p D
  let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
  let K := I ⊔ U
  let UY := U.subgroupOf Y
  let F := L ⊔ UY
  let A := (H.subgroupOf Y).subgroupOf F
  let f := Y.subtype.comp F.subtype
  have hz : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).2,
      (orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).1⟩
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨hDpoint, _hTD, _hTnormal, hUD, _hUnormal, hUodd, _hpart, _hSylow,
    hIpoint, _hInormal, hzI, hKpoint, _hKnorm, hIKnormal, _hgen, _hUprod, _hKprod⟩ :=
    local_theta_auxiliary_construction h.local_datum S hzS hzcenter Y hzY hescape beta hbeta hp
  have hUY : U ≤ Y := hUD.trans inf_le_left
  have hUYodd : Odd (Nat.card UY) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY).toEquiv]
    exact hUodd
  obtain ⟨_hproper, _hYcard, _hlocal, _hcentral, hLnormal, hLstrong,
    _hLclass, _hLtrans, _hXfixed⟩ := leastFailure_local_normalizer_hull h X hXH hXne hXz hescape
  obtain ⟨hFcard, hFrank, hFstrong, _hFtrans, _hFdouble, _hcoreA, _hcorefix⟩ :=
    leastFailure_local_normalizer_odd_join_action h X hXH hXne hXz hescape hrank
      UY hUYodd beta hbeta
  have hf : Function.Injective f := Y.subtype_injective.comp F.subtype_injective
  have hFrange : f.range = F.map Y.subtype := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hIL : I ≤ L.map Y.subtype := by
    rw [internal_involution_hull_image_eq_class_closure Y z hzY]
    apply Subgroup.closure_mono
    rintro a ⟨g, rfl⟩
    exact ⟨⟨g.val, g.property.2⟩, rfl⟩
  have hIF : I ≤ f.range := by
    rw [hFrange]
    exact hIL.trans (Subgroup.map_mono le_sup_left)
  have hUF : U ≤ f.range := by
    rw [hFrange, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hUY]
    exact le_sup_right
  have hKF : K ≤ f.range := sup_le hIF hUF
  let e : F ≃* f.range := MonoidHom.ofInjective hf
  let kR : K →* f.range := K.subtype.codRestrict _ (fun k => hKF k.property)
  let kF : K →* F := e.symm.toMonoidHom.comp kR
  have hkcomp : f.comp kF = K.subtype := by
    ext k
    exact congrArg Subtype.val (e.apply_symm_apply (kR k))
  have hkinj : Function.Injective kF := by
    intro x y hxy
    exact K.subtype_injective (by
      have hh := congrArg f hxy
      change (f.comp kF) x = (f.comp kF) y at hh
      simpa only [hkcomp] using hh)
  let zF : F := ⟨zY, (le_sup_left : L ≤ F) (localPointHull_distinguished_mem zY)⟩
  have hzF : IsInvolution zF := IsInvolution.subtype
    (IsInvolution.subtype hz hzY) _
  have hzAF : zF ∈ A := h.local_datum.distinguished_mem
  have hAcomap : (H ⊓ Y).comap f = A := by
    ext a
    change ((a.val : G) ∈ H ∧ (a.val : G) ∈ Y) ↔ (a.val : G) ∈ H
    exact ⟨And.left, fun ha => ⟨ha, a.val.property⟩⟩
  have hfullclass : f '' conjugacyWithin A zF = conjugacyWithin (H ⊓ Y) z := by
    have hh := strongly_embedded_full_point_class_image f hf (H ⊓ Y)
      (hAcomap.symm ▸ hzAF) hzF
      (hAcomap.symm ▸ native_strong_embedding_of_order_conditions hFstrong)
      (fun _ hx => hIF (Subgroup.subset_closure hx))
    have hfz : f zF = z := rfl
    simpa only [hAcomap, hfz] using hh
  let JF := Subgroup.closure (conjugacyWithin A zF)
  have hJFimage : JF.map f = I := by
    rw [MonoidHom.map_closure, hfullclass]
  let q := QuotientGroup.mk' (CFSG.oddCore F)
  have hqcomm := proper_commuting_images_of_injective hcomm f hf hFcard hFrank A hFstrong
  have hJFelem : IsElementaryAbelian 2 (JF.map q) :=
    involution_class_quotient_elementary A hzAF
      (orderOf_eq_prime hzF.sq_eq_one hzF.ne_one) hqcomm
  let IK := I.subgroupOf K
  let UK := U.subgroupOf K
  let : IK.Normal := hIKnormal
  have hIKimage : IK.map kF = JF := by
    apply Subgroup.map_injective hf
    rw [Subgroup.map_map, hkcomp, Subgroup.map_subgroupOf_eq_of_le le_sup_left, hJFimage]
  let qK := q.comp kF
  have hIKelem : IsElementaryAbelian 2 (IK.map qK) := by
    rw [← Subgroup.map_map, hIKimage]
    exact hJFelem
  let : IsElementaryAbelian 2 (IK.map qK) := hIKelem
  have hUKodd : Odd (Nat.card UK) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : U ≤ K)).toEquiv]
    exact hUodd
  have hKgen : IK ⊔ UK = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self K
  have hqKodd : Odd (Nat.card qK.ker) := injective_odd_quotient_kernel kF hkinj
    (CFSG.oddCore F) (CFSG.ComponentClassification.OddCore.odd_card F)
  obtain ⟨hsol, htwo, hcore⟩ := odd_kernel_image_structure qK hqKodd IK UK hUKodd hKgen
  have hLrank := localNormalizer_internal_hull_rank_two Y z hzY hrank
  let AL := (H.subgroupOf Y).subgroupOf L
  let zL : L := ⟨zY, localPointHull_distinguished_mem zY⟩
  have hILrank := strongly_embedded_point_class_hull_rank AL
    (native_strong_embedding_of_order_conditions hLstrong) hLrank
    (show zL ∈ AL from h.local_datum.distinguished_mem)
    (IsInvolution.subtype (IsInvolution.subtype hz hzY) _)
  let IL := Subgroup.closure (conjugacyWithin AL zL)
  let lG := Y.subtype.comp L.subtype
  have hILimage : IL.map lG ≤ I := by
    rw [MonoidHom.map_closure]
    apply (Subgroup.closure_le _).mpr
    rintro a ⟨b, ⟨c, rfl⟩, rfl⟩
    apply Subgroup.subset_closure
    exact ⟨⟨c.val.val, c.property, c.val.val.property⟩, rfl⟩
  let iG : IL →* I := (lG.comp IL.subtype).codRestrict _
    (fun a => hILimage (Subgroup.mem_map.mpr ⟨a.val, a.property, rfl⟩))
  have hiGinj : Function.Injective iG := by
    intro a b hab
    have hh : (a.val.val.val : G) = b.val.val.val :=
      congrArg (fun a : I => (a : G)) hab
    exact IL.subtype_injective (L.subtype_injective (Y.subtype_injective hh))
  have hIrank : TwoRankAtLeastTwo I := hILrank.map_of_injective iG hiGinj
  have hKrank : TwoRankAtLeastTwo K := hIrank.map_of_injective
    (Subgroup.inclusion (le_sup_left : I ≤ K)) (Subgroup.inclusion_injective _)
  have hclass := localNormalizer_point_class_eq_pair_odd_core_class h.local_datum
    S hzS hzcenter Y hzY hescape beta hbeta
  have hKclass : ∀ v : G, (v ∈ K ∧ IsInvolution v) ↔ v ∈ conjugacyWithin T z := by
    intro v
    constructor
    · rintro ⟨hvK, hvi⟩
      rw [← hclass]
      apply normal_hull_odd_join_point_involution_class H Y z hzY
        h.local_datum.distinguished_mem hz UY hUYodd
        (native_strong_embedding_of_order_conditions hLstrong) v (hKpoint hvK).1
      · rw [← hFrange]
        exact hKF hvK
      · exact hvi
    · intro hv
      have hvI : v ∈ I := Subgroup.subset_closure (hclass.symm ▸ hv)
      refine ⟨(le_sup_left : I ≤ K) hvI, ?_⟩
      obtain ⟨t, rfl⟩ := hv
      have ht2 := order_two_of_mem_pointClass h.local_datum.distinguished_order
        (show (t : G)⁻¹ * z * t ∈ involutionPointClass z from ⟨t, rfl⟩)
      exact ⟨(orderOf_eq_prime_iff.mp ht2).2, (orderOf_eq_prime_iff.mp ht2).1⟩
  exact ⟨hsol, hKrank, htwo, hKclass, kF, hkinj, hkcomp, hqKodd, hIKelem, hcore⟩

end CFSG.ShultStronglyClosedTI.LocalTheta
