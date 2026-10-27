module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.MatAut

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups

theorem exists_conj_eq_on_img_Sgrp {X : Type} [Group X] [Finite X] (S : CubeSetting X) {c : X}
    (hnorm : ∀ x ∈ S.img Sgrp, c * x * c⁻¹ ∈ S.img Sgrp)
    (h1 : ∀ x ∈ S.img Sone, c * x * c⁻¹ ∈ S.img Sone)
    (h6 : ∀ y ∈ S.img Ssix, c * y * c⁻¹ ∈ S.img Ssix) :
    ∃ g ∈ S.img (Sgrp ⊔ Jgrp), ∀ x ∈ S.img Sgrp, c * x * c⁻¹ = g * x * g⁻¹ := by
  let ι : SL(6, ZMod 2) →* X := S.L.subtype.comp S.eL.symm.toMonoidHom
  have hι : Function.Injective ι := by
    intro a b h
    exact S.eL.symm.injective (S.L.subtype_injective h)
  let β : ↥(S.img Sgrp) →* ↥(S.img Sgrp) :=
    MonoidHom.codRestrict ((MulAut.conj c).toMonoidHom.comp (S.img Sgrp).subtype)
      (S.img Sgrp) (fun x => hnorm x x.2)
  have hβ : Function.Injective β := by
    intro x y hxy
    apply Subtype.ext
    have hx : (β x : X) = (β y : X) := congrArg Subtype.val hxy
    change c * (x : X) * c⁻¹ = c * (y : X) * c⁻¹ at hx
    exact mul_left_cancel (mul_right_cancel hx)
  let e : ↥Sgrp ≃* ↥(S.img Sgrp) := Subgroup.equivMapOfInjective Sgrp ι hι
  let α : ↥Sgrp →* ↥Sgrp := (e.symm.toMonoidHom).comp (β.comp e.toMonoidHom)
  have hα : Function.Injective α := by
    intro x y hxy
    have hβe : β (e x) = β (e y) := e.symm.injective hxy
    exact e.injective (hβ hβe)
  have hα_spec : ∀ s : ↥Sgrp, ι (α s : SL(6, ZMod 2)) =
      c * ι (s : SL(6, ZMod 2)) * c⁻¹ := by
    intro s
    have hspec : e (α s) = β (e s) := MulEquiv.apply_symm_apply e (β (e s))
    have hcoee : (e (α s) : X) = ι (α s : SL(6, ZMod 2)) :=
      Subgroup.coe_equivMapOfInjective_apply Sgrp ι hι (α s)
    have hcoes : (e s : X) = ι (s : SL(6, ZMod 2)) :=
      Subgroup.coe_equivMapOfInjective_apply Sgrp ι hι s
    have hβapp : (β (e s) : X) = c * (e s : X) * c⁻¹ := rfl
    rw [← hcoee, hspec, hβapp, hcoes]
  have hα1 : ∀ x : ↥Sgrp, (x : SL(6, ZMod 2)) ∈ Sone →
      ((α x : ↥Sgrp) : SL(6, ZMod 2)) ∈ Sone := by
    intro x hx
    have hxmem : ι (x : SL(6, ZMod 2)) ∈ S.img Sone := by
      change ι (x : SL(6, ZMod 2)) ∈ Sone.map ι
      exact ⟨(x : SL(6, ZMod 2)), hx, rfl⟩
    have hc : c * ι (x : SL(6, ZMod 2)) * c⁻¹ ∈ S.img Sone := h1 _ hxmem
    change c * ι (x : SL(6, ZMod 2)) * c⁻¹ ∈ Sone.map ι at hc
    rw [Subgroup.mem_map] at hc
    obtain ⟨a, ha, haeq⟩ := hc
    have hEq : a = ((α x : ↥Sgrp) : SL(6, ZMod 2)) := by
      apply hι
      rw [haeq, hα_spec x]
    rw [← hEq]
    exact ha
  have hα6 : ∀ x : ↥Sgrp, (x : SL(6, ZMod 2)) ∈ Ssix →
      ((α x : ↥Sgrp) : SL(6, ZMod 2)) ∈ Ssix := by
    intro x hx
    have hxmem : ι (x : SL(6, ZMod 2)) ∈ S.img Ssix := by
      change ι (x : SL(6, ZMod 2)) ∈ Ssix.map ι
      exact ⟨(x : SL(6, ZMod 2)), hx, rfl⟩
    have hc : c * ι (x : SL(6, ZMod 2)) * c⁻¹ ∈ S.img Ssix := h6 _ hxmem
    change c * ι (x : SL(6, ZMod 2)) * c⁻¹ ∈ Ssix.map ι at hc
    rw [Subgroup.mem_map] at hc
    obtain ⟨a, ha, haeq⟩ := hc
    have hEq : a = ((α x : ↥Sgrp) : SL(6, ZMod 2)) := by
      apply hι
      rw [haeq, hα_spec x]
    rw [← hEq]
    exact ha
  obtain ⟨g₀, hg₀, hconj⟩ := exists_conj_eq_of_preserves α hα hα1 hα6
  refine ⟨ι g₀, ?_, ?_⟩
  · change ι g₀ ∈ (Sgrp ⊔ Jgrp).map ι
    exact ⟨g₀, hg₀, rfl⟩
  · intro x hx
    change x ∈ Sgrp.map ι at hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    let s' : ↥Sgrp := ⟨s, hs⟩
    calc c * ι s * c⁻¹ = ι (α s' : SL(6, ZMod 2)) := (hα_spec s').symm
      _ = ι (g₀ * (s' : SL(6, ZMod 2)) * g₀⁻¹) := by rw [hconj s']
      _ = ι g₀ * ι s * (ι g₀)⁻¹ := by rw [map_mul, map_mul, map_inv]

end CFSG.StandardType.FF81.CentE6
