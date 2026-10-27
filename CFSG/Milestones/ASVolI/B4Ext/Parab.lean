module

public import CFSG.Milestones.ASVolI.B4Natural
public import CFSG.Milestones.ASVolI.B4Ext.Flag

public section

namespace CFSG.ASVolI

open CFSG.GroupTheory.GLnTwoSplitting Module

section Parabolic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def burnsideB49x_par_R (φ : Module.Dual (ZMod 2) W) : Subgroup (W ≃ₗ[ZMod 2] W) where
  carrier := {g | (∀ x, φ (g x) = φ x) ∧ ∀ y, φ y = 0 → g y = y}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨fun x => by rw [LinearEquiv.mul_apply, ha, hb],
      fun y hy => by rw [LinearEquiv.mul_apply, hb' y hy, ha' y hy]⟩
  one_mem' := ⟨fun _ => rfl, fun _ _ => rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun x => ?_, fun y hy => ?_⟩
    · have := ha (a⁻¹ x)
      rw [show a (a⁻¹ x) = x from by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl] at this
      exact this.symm
    · exact (LinearEquiv.symm_apply_eq a).2 (ha' y hy).symm

theorem burnsideB49x_par_R_le (φ : Module.Dual (ZMod 2) W) :
    burnsideB49x_par_R φ ≤ burnsideB49_stab φ := fun _ hg => hg.1

theorem burnsideB49x_par_tv_mem_R {φ : Module.Dual (ZMod 2) W} {u : W} (h : φ u = 0) :
    burnsideB49_tv φ u h ∈ burnsideB49x_par_R φ := by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · rw [burnsideB49_tv_apply, map_add, map_smul, h, smul_zero, add_zero]
  · rw [burnsideB49_tv_apply, hy, zero_smul, add_zero]

theorem burnsideB49x_par_mul_self_of_mem_R {φ : Module.Dual (ZMod 2) W} {g : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ burnsideB49x_par_R φ) : g * g = 1 := by
  ext x
  have h : φ (g x + x) = 0 := by rw [map_add, hg.1, zmod_two_add_self]
  have h1 := hg.2 _ h
  rw [map_add, add_comm (g x) x] at h1
  rw [LinearEquiv.mul_apply]
  exact add_right_cancel h1

theorem burnsideB49x_par_R_isPGroup (φ : Module.Dual (ZMod 2) W) :
    IsPGroup 2 (burnsideB49x_par_R φ) := fun g =>
  ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, sq, burnsideB49x_par_mul_self_of_mem_R g.2, Subgroup.coe_one])⟩

theorem burnsideB49x_par_R_normal (φ : Module.Dual (ZMod 2) W) :
    ((burnsideB49x_par_R φ).subgroupOf (burnsideB49_stab φ)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (burnsideB49x_par_R_le φ)]
  intro r g hr hg
  have hg1 := burnsideB49_mem_stab.1 hg
  have hg2 := burnsideB49_mem_stab.1 (inv_mem hg)
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg1, hr.1, hg2]
  · have hy' : φ (g⁻¹ y) = 0 := by rw [hg2, hy]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hr.2 _ hy', ← LinearEquiv.mul_apply,
      mul_inv_cancel]
    rfl

theorem burnsideB49x_par_K_inf_R {φ : Module.Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1) :
    burnsideB49_K φ w₀ ⊓ burnsideB49x_par_R φ = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hK, hR⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_bot]
  ext x
  have h1 : g (x + φ x • w₀) = x + φ x • w₀ := hR.2 _ (burnsideB49_proj_mem φ hw₀ x)
  rw [map_add, map_smul, (burnsideB49_mem_K.1 hK).2] at h1
  exact add_right_cancel h1

theorem burnsideB49x_par_K_sup_R {φ : Module.Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1) :
    burnsideB49_K φ w₀ ⊔ burnsideB49x_par_R φ = burnsideB49_stab φ := by
  refine le_antisymm (sup_le (burnsideB49_K_le_stab φ w₀) (burnsideB49x_par_R_le φ)) ?_
  intro s hs
  have hs' := burnsideB49_mem_stab.1 hs
  have hu : φ (s w₀ + w₀) = 0 := by
    rw [map_add, hs', hw₀]
    exact zmod_two_add_self _
  have hkK : burnsideB49_tv φ (s w₀ + w₀) hu * s ∈ burnsideB49_K φ w₀ := by
    refine ⟨fun x => ?_, ?_⟩
    · rw [LinearEquiv.mul_apply, burnsideB49_tv_apply, map_add, map_smul, hu, smul_zero,
        add_zero, hs']
    · rw [LinearEquiv.mul_apply, burnsideB49_tv_apply, hs', hw₀, one_smul]
      calc s w₀ + (s w₀ + w₀) = (s w₀ + s w₀) + w₀ := by abel
        _ = w₀ := by rw [two_add_self, zero_add]
  have hsk : s = burnsideB49_tv φ (s w₀ + w₀) hu * (burnsideB49_tv φ (s w₀ + w₀) hu * s) := by
    rw [← mul_assoc, burnsideB49_tv_mul_self, one_mul]
  rw [hsk]
  exact mul_mem (Subgroup.mem_sup_right (burnsideB49x_par_tv_mem_R hu))
    (Subgroup.mem_sup_left hkK)

@[expose] noncomputable def burnsideB49x_par_res (φ : Module.Dual (ZMod 2) W) :
    ↥(burnsideB49_stab φ) →* (↥(LinearMap.ker φ) ≃ₗ[ZMod 2] ↥(LinearMap.ker φ)) where
  toFun s := (s : W ≃ₗ[ZMod 2] W).ofSubmodules (LinearMap.ker φ) (LinearMap.ker φ)
    (burnsideB49_map_ker (burnsideB49_mem_stab.1 s.2))
  map_one' := by
    ext w
    rfl
  map_mul' s s' := by
    ext w
    rfl

theorem burnsideB49x_par_le_R_of_normal [FiniteDimensional (ZMod 2) W]
    {φ : Module.Dual (ZMod 2) W} (N : Subgroup ↥(burnsideB49_stab φ)) (hN : N.Normal)
    (hNp : IsPGroup 2 N) : N.map (burnsideB49_stab φ).subtype ≤ burnsideB49x_par_R φ := by
  rintro x ⟨n, hn, rfl⟩
  refine ⟨burnsideB49_mem_stab.1 n.2, fun y hy => ?_⟩
  show (n : W ≃ₗ[ZMod 2] W) y = y
  by_cases hy0 : y = 0
  · rw [hy0, map_zero]
  have h1 : 0 < Module.finrank (ZMod 2) ↥(LinearMap.ker φ) :=
    Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨y, LinearMap.mem_ker.2 hy⟩, fun h => hy0 (congrArg Subtype.val h)⟩
  obtain ⟨y₀, hy₀, hfix⟩ :=
    burnsideB49x_exists_fixed_ne_zero _ (hNp.map (burnsideB49x_par_res φ)) h1
  have hy₀' : (y₀ : W) ≠ 0 := fun h => hy₀ (Subtype.ext h)
  obtain ⟨g, hg, hgy⟩ := burnsideB49_exists_stab_single hy₀' hy0 (LinearMap.mem_ker.1 y₀.2) hy
  have hm : (⟨g, hg⟩ : ↥(burnsideB49_stab φ))⁻¹ * n * ⟨g, hg⟩ ∈ N := hN.conj_mem' n hn _
  have h' : (g⁻¹ * (n : W ≃ₗ[ZMod 2] W) * g) (y₀ : W) = y₀ :=
    congrArg Subtype.val (hfix _ (Subgroup.mem_map_of_mem (burnsideB49x_par_res φ) hm))
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgy] at h'
  have h3 : (n : W ≃ₗ[ZMod 2] W) y = g y₀ := (LinearEquiv.symm_apply_eq g).1 h'
  rw [h3, hgy]

theorem burnsideB49x_par_pCore_eq [FiniteDimensional (ZMod 2) W] (φ : Module.Dual (ZMod 2) W) :
    (CFSG.pCore 2 ↥(burnsideB49_stab φ)).map (burnsideB49_stab φ).subtype =
      burnsideB49x_par_R φ := by
  refine le_antisymm (burnsideB49x_par_le_R_of_normal _ CFSG.pCore_normal CFSG.pCore_isPGroup) ?_
  have hmem : (burnsideB49x_par_R φ).subgroupOf (burnsideB49_stab φ) ∈
      {K : Subgroup ↥(burnsideB49_stab φ) | K.Normal ∧ IsPGroup 2 K} :=
    ⟨burnsideB49x_par_R_normal φ, (burnsideB49x_par_R_isPGroup φ).of_equiv
      (Subgroup.subgroupOfEquivOfLe (burnsideB49x_par_R_le φ)).symm⟩
  calc burnsideB49x_par_R φ
      = ((burnsideB49x_par_R φ).subgroupOf (burnsideB49_stab φ)).map
          (burnsideB49_stab φ).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (burnsideB49x_par_R_le φ)).symm
    _ ≤ (CFSG.pCore 2 ↥(burnsideB49_stab φ)).map (burnsideB49_stab φ).subtype :=
        Subgroup.map_mono (le_sSup hmem)

end Parabolic

end CFSG.ASVolI
