module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalNormalizerOddJoin
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaCentralExtension

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ComponentClassification.TwoRankTransport
open scoped IsMulCommutative

universe u v

variable {G : Type u} [Group G]

theorem numeric_rank_two_of_four [Finite G] (hfour : TwoRankAtLeastTwo G) :
    2 ≤ twoRank G := by
  obtain ⟨E, hcard, hsq⟩ := hfour
  have hE : IsElemAbelian 2 E := by
    refine ⟨isMulCommutative_of_forall_sq_one hsq, ?_⟩
    intro x hx
    exact congrArg Subtype.val (hsq ⟨x, hx⟩)
  exact rank_le (⊤ : Subgroup G) E le_top hE 2 (by norm_num [hcard])

theorem proper_commuting_images_of_injective [Finite G]
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {F : Type u} [Group F] [Finite F] (f : F →* G) (hf : Function.Injective f)
    (hcard : Nat.card F < Nat.card G) (hrank : TwoRankAtLeastTwo F)
    (A : Subgroup F) (hA : fusionStronglyEmbedded A) :
    ∀ a b : F ⧸ CFSG.oddCore F,
      a ∈ A.map (QuotientGroup.mk' (CFSG.oddCore F)) → orderOf a = 2 →
      b ∈ A.map (QuotientGroup.mk' (CFSG.oddCore F)) → orderOf b = 2 → Commute a b := by
  let M := f.range
  let e : F ≃* M := MonoidHom.ofInjective hf
  have hMproper : M < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hmcard : Nat.card M = Nat.card F := (Nat.card_congr e.toEquiv).symm
    rw [htop, Subgroup.card_top] at hmcard
    exact (Nat.ne_of_lt hcard) hmcard.symm
  have hMrank : TwoRankAtLeastTwo M := hrank.map_of_injective e.toMonoidHom e.injective
  have hMA : fusionStronglyEmbedded (A.map e.toMonoidHom) := hA.map_mulEquiv e
  have hcore : (CFSG.oddCore F).map e.toMonoidHom = CFSG.oddCore M :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  let q : F ⧸ CFSG.oddCore F ≃* M ⧸ CFSG.oddCore M :=
    QuotientGroup.congr _ _ e hcore
  have hq : q.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore F)) =
      (QuotientGroup.mk' (CFSG.oddCore M)).comp e.toMonoidHom := by
    ext x
    exact QuotientGroup.congr_mk' _ _ e hcore x
  have hAM :
      (A.map (QuotientGroup.mk' (CFSG.oddCore F))).map q.toMonoidHom =
        (A.map e.toMonoidHom).map (QuotientGroup.mk' (CFSG.oddCore M)) := by
    rw [Subgroup.map_map, hq, ← Subgroup.map_map]
  have hsmall := hcomm M hMproper (numeric_rank_two_of_four hMrank)
    (A.map e.toMonoidHom) hMA
  intro a b ha ha2 hb hb2
  have hqa : q a ∈ (A.map e.toMonoidHom).map (QuotientGroup.mk' (CFSG.oddCore M)) := by
    rw [← hAM]
    exact Subgroup.mem_map_of_mem q.toMonoidHom ha
  have hqb : q b ∈ (A.map e.toMonoidHom).map (QuotientGroup.mk' (CFSG.oddCore M)) := by
    rw [← hAM]
    exact Subgroup.mem_map_of_mem q.toMonoidHom hb
  have hxy := hsmall (q a) (q b) hqa ((q.orderOf_eq a).trans ha2)
    hqb ((q.orderOf_eq b).trans hb2)
  apply q.injective
  simpa only [map_mul] using hxy.eq

theorem involution_class_quotient_elementary [Finite G]
    (A : Subgroup G) {z : G} (hzA : z ∈ A) (hz : orderOf z = 2)
    (hcomm : ∀ a b : G ⧸ CFSG.oddCore G,
      a ∈ A.map (QuotientGroup.mk' (CFSG.oddCore G)) → orderOf a = 2 →
      b ∈ A.map (QuotientGroup.mk' (CFSG.oddCore G)) → orderOf b = 2 → Commute a b) :
    IsElementaryAbelian 2
      ((Subgroup.closure (conjugacyWithin A z)).map
        (QuotientGroup.mk' (CFSG.oddCore G))) := by
  let q := QuotientGroup.mk' (CFSG.oddCore G)
  have horder : ∀ a ∈ conjugacyWithin A z, orderOf (q a) = 2 := by
    intro a ha
    have ha2 : orderOf a = 2 := by
      obtain ⟨g, hg⟩ := ha
      exact order_two_of_mem_pointClass hz ⟨g, hg⟩
    have hker : Odd (Nat.card q.ker) := by
      rw [QuotientGroup.ker_mk']
      exact CFSG.ComponentClassification.OddCore.odd_card G
    have hai : IsInvolution a :=
      ⟨(orderOf_eq_prime_iff.mp ha2).2, (orderOf_eq_prime_iff.mp ha2).1⟩
    have hi := CFSG.ProperTwoGeneratedCore.involution_image_of_odd_kernel q hker hai
    exact orderOf_eq_prime hi.sq_eq_one hi.ne_one
  have hmem : conjugacyWithin A z ⊆ A := by
    rintro a ⟨g, rfl⟩
    exact A.mul_mem (A.mul_mem (A.inv_mem g.property) hzA) g.property
  rw [MonoidHom.map_closure]
  apply square_one_commuting_closure_elementary
  · rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ _
    exact hcomm _ _ (Subgroup.mem_map_of_mem q (hmem hx)) (horder x hx)
      (Subgroup.mem_map_of_mem q (hmem hy)) (horder y hy)
  · rintro a ⟨x, hx, rfl⟩
    exact (orderOf_eq_prime_iff.mp (horder x hx)).1

theorem strongly_embedded_point_class_hull_rank [Finite G]
    (A : Subgroup G) (hA : CFSG.BenderSuzuki.IsStronglyEmbedded A)
    (hrank : TwoRankAtLeastTwo G) {z : G} (hzA : z ∈ A) (hz : IsInvolution z) :
    TwoRankAtLeastTwo (Subgroup.closure (conjugacyWithin A z)) := by
  obtain ⟨P, hPA⟩ := hA.containsSylowTwo
  obtain ⟨E, hcard, hsq⟩ := twoRankAtLeastTwo_of_contains_sylow P hPA hrank
  let I := Subgroup.closure (conjugacyWithin A z)
  let f : E →* G := A.subtype.comp E.subtype
  have hmem : ∀ e : E, f e ∈ I := by
    intro e
    by_cases he : f e = 1
    · rw [he]
      exact I.one_mem
    have hei : IsInvolution (f e) := ⟨he, by
      simpa only [map_pow, map_one] using congrArg f (hsq e)⟩
    obtain ⟨a, ha, hea⟩ := hA.involutions_conjugate_in hzA hz e.val.property hei
    exact Subgroup.subset_closure ⟨⟨a, ha⟩, hea⟩
  let g : E →* I := f.codRestrict I hmem
  have hinj : Function.Injective g := by
    intro a b hab
    have hh : (a.val.val : G) = b.val.val :=
      congrArg (fun x : I => (x : G)) hab
    apply Subtype.ext
    exact Subtype.ext hh
  have hErank : TwoRankAtLeastTwo E := by
    refine ⟨⊤, by simpa only [Subgroup.card_top] using hcard, ?_⟩
    intro x
    exact Subtype.ext (hsq x.val)
  exact hErank.map_of_injective g hinj

theorem normal_hull_odd_join_point_involution_class [Finite G]
    (H Y : Subgroup G) (z : G) (hzY : z ∈ Y)
    (hzH : z ∈ H) (hz : IsInvolution z)
    (U : Subgroup Y) (hUodd : Odd (Nat.card U))
    (hstrong : CFSG.BenderSuzuki.IsStronglyEmbedded
      ((H.subgroupOf Y).subgroupOf (involutionPointHull (⟨z, hzY⟩ : Y))))
    (v : G) (hvH : v ∈ H)
    (hvF : v ∈ (involutionPointHull (⟨z, hzY⟩ : Y) ⊔ U).map Y.subtype)
    (hvi : IsInvolution v) : v ∈ conjugacyWithin (H ⊓ Y) z := by
  let zY : Y := ⟨z, hzY⟩
  let L := involutionPointHull zY
  let F := L ⊔ U
  let : L.Normal := minimalLocalFailure_hull_normal zY
  obtain ⟨vY, hvY, hvimage⟩ := Subgroup.mem_map.mp hvF
  change (vY : G) = v at hvimage
  have hvorder : orderOf vY = 2 := by
    exact (Subgroup.orderOf_coe vY).symm.trans
      (hvimage ▸ orderOf_eq_prime hvi.sq_eq_one hvi.ne_one)
  have hvL : vY ∈ L := localNormalizer_normal_odd_join_involution_mem L U hUodd
    ⟨vY, hvY⟩ ((Subgroup.orderOf_coe (⟨vY, hvY⟩ : F)).symm.trans hvorder)
  let vL : L := ⟨vY, hvL⟩
  let zL : L := ⟨zY, localPointHull_distinguished_mem zY⟩
  have hvpoint : vL ∈ (H.subgroupOf Y).subgroupOf L := by
    change (vY : G) ∈ H
    rwa [hvimage]
  have hzpoint : zL ∈ (H.subgroupOf Y).subgroupOf L := hzH
  have hzL : IsInvolution zL := IsInvolution.subtype (IsInvolution.subtype hz hzY) _
  have hvLI : IsInvolution vL := by
    have hh : IsInvolution vY := IsInvolution.subtype (hvimage.symm ▸ hvi) vY.property
    exact IsInvolution.subtype hh hvL
  obtain ⟨a, ha, hconj⟩ := hstrong.involutions_conjugate_in hzpoint hzL hvpoint hvLI
  refine ⟨⟨a.val.val, ha, a.val.property⟩, ?_⟩
  exact (congrArg (fun x : L => (x.val : G)) hconj).trans hvimage

end CFSG.ShultStronglyClosedTI.LocalTheta
