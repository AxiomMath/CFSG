module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureOddCoreTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingConjugacy
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem minimalLocalFailure_hull_map {Q : Type*} [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (z : G) :
    (involutionPointHull z).map f = involutionPointHull (f z) := by
  unfold involutionPointHull
  rw [f.map_closure]
  congr 1
  ext q
  constructor
  · rintro ⟨x, ⟨g, rfl⟩, rfl⟩
    exact ⟨f g, by simp only [rightConjugateElem, map_mul, map_inv]⟩
  · rintro ⟨qg, rfl⟩
    obtain ⟨g, rfl⟩ := hf qg
    exact ⟨rightConjugateElem z g, ⟨g, rfl⟩,
      by simp only [rightConjugateElem, map_mul, map_inv]⟩

variable [Finite G]

theorem minimalLocalFailure_stronglyEmbedded_of_all_involutions
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hall : ∀ x : G, orderOf x = 2 → x ∈ involutionPointClass z) :
    fusionStronglyEmbedded H := by
  apply order_strong_embedding_of_native
  refine ⟨h.proper, ⟨z, h.distinguished_mem, ?_⟩, ?_⟩
  · exact ⟨(orderOf_eq_prime_iff.mp h.distinguished_order).2,
      (orderOf_eq_prime_iff.mp h.distinguished_order).1⟩
  · intro g hg x hxH hxright hxI
    obtain ⟨a, rfl⟩ := hall x (orderOf_eq_prime hxI.sq_eq_one hxI.ne_one)
    have haH : a ∈ H := (pointClass_conjugate_mem_iff h a).mp hxH
    have hconj : rightConjugateElem (rightConjugateElem z a) g⁻¹ ∈ H :=
      rightConjugateElem_mem_of_mem_rightConjugate (by simpa only [inv_inv] using hxright)
    rw [rightConjugateElem_comp] at hconj
    have hagH : a * g⁻¹ ∈ H := (pointClass_conjugate_mem_iff h _).mp hconj
    have hginv : g⁻¹ ∈ H := by
      simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem haH) hagH
    exact hg (H.inv_mem_iff.mp hginv)

theorem minimalLocalFailure_not_ambient_stronglyEmbedded
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z) :
    ¬ fusionStronglyEmbedded H := by
  intro hstrong
  apply h.failure
  rw [minimalLocalFailure_hull_eq_top h]
  have himage : H.map (Subgroup.topEquiv.symm : G ≃* (⊤ : Subgroup G)).toMonoidHom =
      H.subgroupOf (⊤ : Subgroup G) := by
    ext x
    rw [Subgroup.mem_map_equiv]
    rfl
  rw [← himage]
  exact hstrong.map_mulEquiv Subgroup.topEquiv.symm

omit [Finite G] in
theorem minimalLocalFailure_central_image_all_involutions
    {Q : Type*} [Group Q] [Finite Q] (f : G →* Q) (hf : Function.Surjective f)
    {z : G} (hhull : involutionPointHull z = ⊤) (hfz : orderOf (f z) = 2)
    (hcentral : f z ∈ Subgroup.center Q) :
    ∀ q : Q, orderOf q = 2 → q = f z := by
  have hgen : involutionPointHull (f z) = ⊤ := by
    rw [← minimalLocalFailure_hull_map f hf z, hhull,
      Subgroup.map_top_of_surjective f hf]
  have hclass : involutionPointClass (f z) ⊆ Subgroup.zpowers (f z) := by
    rintro q ⟨g, rfl⟩
    change rightConjugateElem (f z) g ∈ Subgroup.zpowers (f z)
    have heq : rightConjugateElem (f z) g = f z := by
      dsimp only [rightConjugateElem]
      rw [mul_assoc, ← Subgroup.mem_center_iff.mp hcentral g, inv_mul_cancel_left]
    rw [heq]
    exact Subgroup.mem_zpowers (f z)
  have htop : Subgroup.zpowers (f z) = ⊤ := by
    apply top_le_iff.mp
    rw [← hgen]
    exact (Subgroup.closure_le _).mpr hclass
  intro q hq
  have hqmem : q ∈ Subgroup.zpowers (f z) := by
    rw [htop]
    exact Subgroup.mem_top q
  rcases CFSG.ProperTwoGeneratedCore.involution_zpowers_elements hfz hqmem with hone | heq
  · simp only [hone, orderOf_one] at hq
    omega
  · exact heq

theorem minimalLocalFailure_odd_core_quotient_stronglyEmbedded
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hne : oddCore G ≠ ⊥) (hproper : H ⊔ oddCore G ≠ ⊤) :
    fusionStronglyEmbedded (H.map (QuotientGroup.mk' (oddCore G))) := by
  let N := oddCore G
  let f := QuotientGroup.mk' N
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card G
  obtain ⟨S, hzS, hcenter⟩ := h.central_sylow
  have hcomm : ∀ s ∈ (S : Subgroup G), Commute z s := by
    intro s hs
    exact (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hcenter (⟨s, hs⟩ : (S : Subgroup G)))).symm
  obtain ⟨hlocal, T, _hTimage, hzT, hcentral⟩ :=
    CFSG.ProperTwoGeneratedCore.local_involution_point_embedding_odd_quotient_central_sylow
      h.local_datum N hNodd hproper S hzS hcomm
  have hcentralSylow : InvolutionPointCentralSylow (f z) := by
    refine ⟨T, hzT, ?_⟩
    apply Subgroup.mem_center_iff.mpr
    intro t
    apply Subtype.ext
    exact (hcentral t t.property).symm.eq
  have hcardN : 1 < Nat.card N := by
    have hpos : 0 < Nat.card N := Nat.card_pos
    have hnotone : Nat.card N ≠ 1 := fun heq => hne (Subgroup.card_eq_one.mp heq)
    omega
  have hcard : Nat.card (G ⧸ N) < Nat.card G := by
    calc
      Nat.card (G ⧸ N) < Nat.card (G ⧸ N) * Nat.card N :=
        (Nat.lt_mul_iff_one_lt_right Nat.card_pos).mpr hcardN
      _ = Nat.card G := (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
  have hgen : involutionPointHull (f z) = ⊤ := by
    rw [← minimalLocalFailure_hull_map f (QuotientGroup.mk'_surjective N) z,
      minimalLocalFailure_hull_eq_top h,
      Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective N)]
  have hstrong := h.smaller (G ⧸ N) hcard (H.map f) (f z) hlocal hcentralSylow
  rw [hgen] at hstrong
  have himage : ((H.map f).subgroupOf (⊤ : Subgroup (G ⧸ N))).map
      Subgroup.topEquiv.toMonoidHom = H.map f := by
    change ((H.map f).subgroupOf (⊤ : Subgroup (G ⧸ N))).map
      (⊤ : Subgroup (G ⧸ N)).subtype = H.map f
    rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]
  have htransport := hstrong.map_mulEquiv Subgroup.topEquiv
  rwa [himage] at htransport

theorem minimalLocalFailure_odd_core_eq_bot
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z) :
    oddCore G = ⊥ := by
  by_contra hne
  let N := oddCore G
  let f := QuotientGroup.mk' N
  have hodd : Odd (Nat.card f.ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.ComponentClassification.OddCore.odd_card G
  have hz : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).2,
      (orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).1⟩
  have hfz := CFSG.ProperTwoGeneratedCore.involution_image_of_odd_kernel f hodd hz
  have hall : ∀ x : G, orderOf x = 2 → x ∈ involutionPointClass z := by
    intro x hxorder
    have hx : IsInvolution x :=
      ⟨(orderOf_eq_prime_iff.mp hxorder).2, (orderOf_eq_prime_iff.mp hxorder).1⟩
    apply (CFSG.ProperTwoGeneratedCore.involution_point_class_image_iff f
      (QuotientGroup.mk'_surjective N) hodd hz hx).mp
    by_cases hcover : H ⊔ N = ⊤
    · have hcentral := minimalLocalFailure_odd_core_cover_image_central h.local_datum hcover
      have hfx := CFSG.ProperTwoGeneratedCore.involution_image_of_odd_kernel f hodd hx
      have heq := minimalLocalFailure_central_image_all_involutions f
        (QuotientGroup.mk'_surjective N) (minimalLocalFailure_hull_eq_top h)
        (orderOf_eq_prime hfz.sq_eq_one hfz.ne_one) hcentral (f x)
        (orderOf_eq_prime hfx.sq_eq_one hfx.ne_one)
      rw [heq]
      exact distinguished_mem_pointClass (f z)
    · have hstrong := native_strong_embedding_of_order_conditions
        (minimalLocalFailure_odd_core_quotient_stronglyEmbedded h hne hcover)
      have hfx := CFSG.ProperTwoGeneratedCore.involution_image_of_odd_kernel f hodd hx
      obtain ⟨g, hg⟩ := hstrong.involutions_conjugate hfz hfx
      exact ⟨g, hg⟩
  exact minimalLocalFailure_not_ambient_stronglyEmbedded h
    (minimalLocalFailure_stronglyEmbedded_of_all_involutions h.local_datum hall)

theorem minimalLocalFailure_involution_hull_and_cores
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z) :
    involutionPointHull z = ⊤ ∧ oddCore G = ⊥ ∧ CFSG.pCore 2 G = ⊥ :=
  ⟨minimalLocalFailure_hull_eq_top h, minimalLocalFailure_odd_core_eq_bot h,
    minimalLocalFailure_two_core_eq_bot h⟩

end CFSG.ShultStronglyClosedTI
