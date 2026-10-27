module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflSteps

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7CTrickAux_conj_linRefl {p : ℕ} [Fact p.Prime] {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] {r : W ≃ₗ[ZMod p] W}
    (hr : GGLinRefl r) (g : W ≃ₗ[ZMod p] W) : GGLinRefl (g * r * g⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [show g * r * g⁻¹ * (g * r * g⁻¹) = g * (r * r) * g⁻¹ by group, hr.1, mul_one,
      mul_inv_cancel]
  · have hmap : ggLinMove (g * r * g⁻¹) = (ggLinMove r).map g.toLinearMap := by
      rw [ggLinMove, ggLinMove]
      have hcomp : (g * r * g⁻¹).toLinearMap - LinearMap.id =
          g.toLinearMap.comp ((r.toLinearMap - LinearMap.id).comp g⁻¹.toLinearMap) := by
        ext v
        simp [LinearEquiv.mul_apply, map_sub]
      rw [hcomp, LinearMap.range_comp, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr g⁻¹.surjective, Submodule.map_top]
    rw [hmap]
    have e := Submodule.equivMapOfInjective g.toLinearMap g.injective (ggLinMove r)
    rw [← LinearEquiv.finrank_eq e, hr.2]

private theorem hdRo7CTrickAux_refl_of_form {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {r : V ≃ₗ[ZMod p] V} {u : V} {φ : V →ₗ[ZMod p] ZMod p}
    (hform : ∀ v, r v = v - φ v • u) (hφu : φ u = 2) {x : V} (hx : φ x = 1) (hu : u ≠ 0) :
    GGLinRefl r := by
  have hru : r u = -u := by
    rw [hform u, hφu]
    module
  have hsq : r * r = 1 := by
    ext v
    change r (r v) = v
    calc r (r v) = r (v - φ v • u) := by rw [hform v]
      _ = r v - φ v • r u := by rw [map_sub, map_smul]
      _ = (v - φ v • u) - φ v • (-u) := by rw [hform v, hru]
      _ = v := by module
  refine ⟨hsq, ?_⟩
  have hrange : ggLinMove r = Submodule.span (ZMod p) {u} := by
    rw [ggLinMove]
    apply le_antisymm
    · rintro w ⟨v, rfl⟩
      rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply, hform v]
      have h1 : v - φ v • u - v = -(φ v) • u := by module
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
    · rw [Submodule.span_le]
      rintro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      refine ⟨-x, ?_⟩
      rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply, map_neg, hform x,
        hx, one_smul]
      abel
  rw [hrange, finrank_span_singleton hu]

theorem c2_reflTrick_holds : C2ReflTrickLeaf := by
  unfold C2ReflTrickLeaf
  intro hS p hp hp3 n hn V instACG instMod b A hP hStab r u φ hnf h hsp hφhu hφhinu
  obtain ⟨hrA, hform, hφu, hφ0, hu0⟩ := hnf
  have hu : u ≠ 0 := fun h0 => hu0 (by rw [h0, map_zero])
  have hreflr : GGLinRefl r := hdRo7CTrickAux_refl_of_form hform hφu hφ0 hu
  have hrr : r * r = 1 := hreflr.1
  have hrr_apply : ∀ v, r (r v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, hrr]
    rfl
  have hhA : h ∈ A := hP h hsp
  obtain ⟨σ, c, hσ0, hc0, _hcpm, hact⟩ := hsp
  have hfix0 : h (b 0) = b 0 := by rw [hact 0, hσ0, hc0, one_smul]
  have hifix0 : h⁻¹ (b 0) = b 0 := by
    change h.symm (b 0) = b 0
    apply h.injective
    rw [LinearEquiv.apply_symm_apply, hfix0]
  have hrinv : r⁻¹ = r := by
    rw [← mul_one r⁻¹, ← hrr, ← mul_assoc, inv_mul_cancel, one_mul]
  set ρ : V ≃ₗ[ZMod p] V := r * h * r * h⁻¹ * r with hρdef
  have hρeq : ρ = (r * h) * r * (r * h)⁻¹ := by
    rw [hρdef, mul_inv_rev, hrinv]
    group
  have hρrefl : GGLinRefl ρ := by
    rw [hρeq]
    exact hdRo7CTrickAux_conj_linRefl hreflr (r * h)
  have hρA : ρ ∈ A := by
    rw [hρdef]
    exact A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem hrA hhA) hrA) (A.inv_mem hhA)) hrA
  have hr_b0 : r (b 0) = b 0 - u := by rw [hform (b 0), hφ0, one_smul]
  have hr_u : r u = -u := by rw [hform u, hφu]; module
  have hρfix : ρ (b 0) = b 0 := by
    rw [hρdef]
    simp only [LinearEquiv.mul_apply]
    rw [hr_b0, map_sub, hifix0]
    have e3 : r (b 0 - h⁻¹ u) = b 0 - h⁻¹ u := by
      rw [hform]
      have hphi : φ (b 0 - h⁻¹ u) = 0 := by rw [map_sub, hφ0, hφhinu, sub_self]
      rw [hphi, zero_smul, sub_zero]
    rw [e3]
    have e4 : h (b 0 - h⁻¹ u) = b 0 - u := by
      change h (b 0 - h.symm u) = b 0 - u
      rw [map_sub, hfix0, LinearEquiv.apply_symm_apply]
    rw [e4]
    have e5 : r (b 0 - u) = b 0 := by
      rw [map_sub, hr_b0, hr_u]
      abel
    rw [e5]
  have hρSP : C2SP p b ρ := hStab ρ hρA hρfix
  set w : V := r (h u) with hwdef
  have hw : w = h u - u := by
    rw [hwdef, hform (h u), hφhu, one_smul]
  have hρw : ρ w = -w := by
    rw [hρdef, hwdef]
    change r (h (r (h.symm (r (r (h u)))))) = -(r (h u))
    rw [hrr_apply, LinearEquiv.symm_apply_apply, hr_u, map_neg, map_neg]
  rcases eq_or_ne w 0 with hw0 | hw0
  · have hzu : h u - u = 0 := hw.symm.trans hw0
    rw [hzu]
    simp
  · obtain ⟨_, hcard⟩ := hS p hp3 n hn V b ρ hρSP hρrefl w hw0 hρw
    rwa [hw] at hcard

end CFSG.StandardType.HdRo7C
