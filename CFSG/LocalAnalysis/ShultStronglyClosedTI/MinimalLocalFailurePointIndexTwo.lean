module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFullFusion
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureElementTransfer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSimple

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem two_element_conjugates_into_sylow_overgroup
    (S : Sylow 2 G) (M : Subgroup G) (hSM : (S : Subgroup G) ≤ M)
    (x : G) (hxM : x ∈ M) (hx : ∃ n : ℕ, orderOf x = 2 ^ n) :
    ∃ a ∈ M, rightConjugateElem x a ∈ (S : Subgroup G) := by
  let xM : M := ⟨x, hxM⟩
  obtain ⟨n, hn⟩ := hx
  have horder : orderOf xM = 2 ^ n := (Subgroup.orderOf_coe xM).symm.trans hn
  have htwo : IsPGroup 2 (Subgroup.zpowers xM) := IsPGroup.of_card (by
    rw [Nat.card_zpowers, horder])
  obtain ⟨P, hP⟩ := htwo.exists_le_sylow
  let T : Sylow 2 M := S.subtype hSM
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq M P T
  have hxa : a * xM * a⁻¹ ∈ (T : Subgroup M) := by
    rw [← ha]
    change a * xM * a⁻¹ ∈ (P : Subgroup M).map (MulAut.conj a).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨xM, hP (Subgroup.mem_zpowers xM), rfl⟩
  refine ⟨(a : G)⁻¹, M.inv_mem a.property, ?_⟩
  have hxaS : (a : G) * x * (a : G)⁻¹ ∈ (S : Subgroup G) := hxa
  simpa only [rightConjugateElem, inv_inv] using hxaS

theorem element_fusion_in_overgroup_of_full_subgroup_fusion
    (S : Sylow 2 G) (M : Subgroup G) (hSM : (S : Subgroup G) ≤ M)
    (hfusion : ∀ (X : Subgroup G), X ≤ (S : Subgroup G) → ∀ g : G,
      rightConjugate X g ≤ (S : Subgroup G) →
        ∃ c ∈ M, ∀ x ∈ X, rightConjugateElem x c = rightConjugateElem x g) :
    ∀ x : G, x ∈ M → (∃ n : ℕ, orderOf x = 2 ^ n) →
      ∀ g : G, g⁻¹ * x * g ∈ M → ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m := by
  intro x hxM hx g hxgM
  obtain ⟨a, haM, hxaS⟩ := two_element_conjugates_into_sylow_overgroup S M hSM x hxM hx
  have hxgorder : ∃ n : ℕ, orderOf (rightConjugateElem x g) = 2 ^ n := by
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    simpa only [rightConjugateElem, MulAut.conj_apply, inv_inv] using
      ((MulAut.conj g⁻¹).orderOf_eq x).trans hn
  obtain ⟨b, hbM, hxgbS⟩ := two_element_conjugates_into_sylow_overgroup S M hSM
    (rightConjugateElem x g) hxgM hxgorder
  let xa := rightConjugateElem x a
  let d := a⁻¹ * g * b
  let X := Subgroup.zpowers xa
  have hX : X ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr hxaS
  have hxad : rightConjugateElem xa d = rightConjugateElem (rightConjugateElem x g) b := by
    unfold xa d rightConjugateElem
    group
  have hXd : rightConjugate X d ≤ (S : Subgroup G) := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨k, rfl⟩ := hv
    change (MulAut.conj d⁻¹).toMonoidHom (xa ^ k) ∈ (S : Subgroup G)
    rw [map_zpow]
    apply (S : Subgroup G).zpow_mem
    have hxadS : rightConjugateElem xa d ∈ (S : Subgroup G) := hxad.symm ▸ hxgbS
    simpa only [rightConjugateElem, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv] using hxadS
  obtain ⟨c, hcM, hxc⟩ := hfusion X hX d hXd
  have hxa : rightConjugateElem xa c = rightConjugateElem (rightConjugateElem x g) b :=
    (hxc xa (Subgroup.mem_zpowers xa)).trans hxad
  have hconj : rightConjugateElem x (a * c * b⁻¹) = rightConjugateElem x g := by
    have heq := congrArg (fun y : G => b * y * b⁻¹) hxa
    simpa only [xa, rightConjugateElem, mul_inv_rev, inv_inv, mul_assoc,
      mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_inv_cancel, mul_one] using heq
  exact ⟨a * c * b⁻¹, M.mul_mem (M.mul_mem haM hcM) (M.inv_mem hbM), hconj.symm⟩

universe u

theorem minimalLocalFailure_point_stabilizer_no_index_two_subgroup
    {Y : Type u} [Group Y] [Finite Y] {H : Subgroup Y} {z : Y}
    (h : MinimalInvolutionPointLocalFailure H z) :
    ∀ K : Subgroup H, K.index ≠ 2 := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hSH : (S : Subgroup Y) ≤ H := by
    intro s hs
    apply point_centralizer_le h.local_datum
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzcenter (⟨s, hs⟩ : (S : Subgroup Y))))
  have hfull := unique_central_sylow_involution_full_fusion_control S H hSH z hzS hzcenter
    h.local_datum.distinguished_order h.local_datum.unique_containment
  have helement := element_fusion_in_overgroup_of_full_subgroup_fusion S H hSH hfull
  intro K hK
  obtain ⟨N, hNnormal, hNindex⟩ := element_fusion_index_two_transfer_internal S H hSH helement K hK
  obtain ⟨hsimple, hnonab⟩ := minimalLocalFailure_nonabelian_simple h
  let : IsSimpleGroup Y := hsimple
  let : N.Normal := hNnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · have hcard : Nat.card Y = 2 := by simpa only [hbot, Subgroup.index_bot] using hNindex
    let : IsMulCommutative Y := (isCyclic_of_prime_card hcard).isMulCommutative
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (mul_comm a b)
  · rw [htop, Subgroup.index_top] at hNindex
    exact (by decide : (1 : ℕ) ≠ 2) hNindex

end CFSG.ShultStronglyClosedTI
