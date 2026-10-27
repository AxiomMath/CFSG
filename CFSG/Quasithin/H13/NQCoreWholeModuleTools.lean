module

public import CFSG.Quasithin.H13.NQCoreIntrinsicAction

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup Module
open CFSG.Quasithin.SteinbergBQ (commSpan)
open scoped IsMulCommutative commutatorElement

variable {Q : Type*} [Group Q] (V : Subgroup Q) [V.Normal] [IsMulCommutative ↥V]
  [Module (ZMod 2) (Additive ↥V)]

omit [V.Normal] in
theorem mulAutToGL_injective : Function.Injective (mulAutToGL V) := by
  intro σ τ h
  ext v
  have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V) =>
    (g : Additive ↥V →ₗ[ZMod 2] Additive ↥V) (Additive.ofMul v)) h
  exact congrArg Subtype.val (Additive.ofMul.injective h1)

theorem ker_conjGL : (conjGL V).ker = centralizer (V : Set Q) := by
  ext g
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro hg v hv
    have h1 := congrArg (fun γ : LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V) =>
      (γ : Additive ↥V →ₗ[ZMod 2] Additive ↥V) (Additive.ofMul ⟨v, hv⟩)) hg
    simp only [conjGL_apply, Units.val_one, Module.End.one_apply] at h1
    have h2 := congrArg Subtype.val (Additive.ofMul.injective h1)
    simp only [MulAut.conjNormal_apply] at h2
    calc v * g = g * v * g⁻¹ * g := by rw [h2]
      _ = g * v := by group
  · intro hg
    apply Units.ext
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ : ∃ v : ↥V, Additive.ofMul v = w := ⟨Additive.toMul w, rfl⟩
    rw [conjGL_apply, Units.val_one, Module.End.one_apply]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← hg v v.2, mul_inv_cancel_right]

theorem commSpan_map_conjGL_eq_top {Y : Subgroup Q} (hVY : ⁅V, Y⁆ = V) :
    commSpan (Y.map (conjGL V)) = ⊤ := by
  have hle : ⁅V, Y⁆ ≤ V := hVY.le
  have hcl : ⁅V, Y⁆ = closure {g | ∃ a ∈ V, ∃ y ∈ Y, ⁅a, y⁆ = g} := Subgroup.commutator_def V Y
  have key : ∀ g ∈ closure {g | ∃ a ∈ V, ∃ y ∈ Y, ⁅a, y⁆ = g}, ∀ hgV : g ∈ V,
      Additive.ofMul (⟨g, hgV⟩ : ↥V) ∈ commSpan (Y.map (conjGL V)) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg' =>
      intro hgV
      obtain ⟨a, ha, y, hy, rfl⟩ := hg'
      have hsub := SteinbergBQ.sub_mem_commSpan (Q := Y.map (conjGL V)) ⟨y, hy, rfl⟩
        (Additive.ofMul (⟨a, ha⟩ : ↥V))
      have heq : Additive.ofMul (⟨⁅a, y⁆, hgV⟩ : ↥V) =
          -(((conjGL V y : LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)) :
            Additive ↥V →ₗ[ZMod 2] Additive ↥V) (Additive.ofMul ⟨a, ha⟩) -
              Additive.ofMul ⟨a, ha⟩) := by
        rw [conjGL_apply, neg_sub, ← ofMul_div]
        congr 1
        apply Subtype.ext
        simp only [commutatorElement_def, div_eq_mul_inv, Subgroup.coe_mul,
          Subgroup.coe_inv, MulAut.conjNormal_apply, mul_inv_rev, inv_inv, mul_assoc]
      rw [heq]
      exact neg_mem hsub
    | one =>
      intro _
      exact zero_mem _
    | mul g h hg hh ihg ihh =>
      intro _
      have hgV : g ∈ V := hle (hcl ▸ hg)
      have hhV : h ∈ V := hle (hcl ▸ hh)
      have h1 : Additive.ofMul (⟨g * h, V.mul_mem hgV hhV⟩ : ↥V) =
          Additive.ofMul (⟨g, hgV⟩ : ↥V) + Additive.ofMul (⟨h, hhV⟩ : ↥V) := by
        rw [← ofMul_mul]
        rfl
      rw [h1]
      exact add_mem (ihg hgV) (ihh hhV)
    | inv g hg ihg =>
      intro _
      have hgV : g ∈ V := hle (hcl ▸ hg)
      have h1 : Additive.ofMul (⟨g⁻¹, V.inv_mem hgV⟩ : ↥V) = -Additive.ofMul (⟨g, hgV⟩ : ↥V) := by
        rw [← ofMul_inv]
        rfl
      rw [h1]
      exact neg_mem (ihg hgV)
  rw [eq_top_iff]
  intro w _
  have hw : ((Additive.toMul w : ↥V) : Q) ∈ closure {g | ∃ a ∈ V, ∃ y ∈ Y, ⁅a, y⁆ = g} := by
    rw [← hcl, hVY]
    exact (Additive.toMul w).2
  exact key _ hw (Additive.toMul w).2

theorem isPGroup_quotient_map_conjGL {Y S : Subgroup Q} [Y.Normal] (hS : IsPGroup 2 S)
    (hYS : Y ⊔ S = ⊤) :
    ∃ _ : ((Y.map (conjGL V)).subgroupOf (conjGL V).range).Normal,
      IsPGroup 2 (↥(conjGL V).range ⧸ (Y.map (conjGL V)).subgroupOf (conjGL V).range) := by
  have hn : ((Y.map (conjGL V)).subgroupOf (conjGL V).range).Normal := by
    have h1 : (Y.map (conjGL V).rangeRestrict).Normal :=
      (inferInstance : Y.Normal).map _ (conjGL V).rangeRestrict_surjective
    have h2 : Y.map (conjGL V).rangeRestrict = (Y.map (conjGL V)).subgroupOf (conjGL V).range := by
      ext ⟨γ, hγ⟩
      simp only [mem_map, mem_subgroupOf]
      constructor
      · rintro ⟨y, hy, hyγ⟩
        exact ⟨y, hy, congrArg Subtype.val hyγ⟩
      · rintro ⟨y, hy, hyγ⟩
        exact ⟨y, hy, Subtype.ext hyγ⟩
    rw [← h2]
    exact h1
  refine ⟨hn, fun z => ?_⟩
  obtain ⟨⟨γ, hγ⟩, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨g, rfl⟩ := hγ
  have hg : g ∈ Y ⊔ S := hYS ▸ mem_top g
  obtain ⟨y, hy, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  refine ⟨k, ?_⟩
  have hs1 : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hmem : (y * s) ^ 2 ^ k ∈ Y := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff y).mpr hy, one_mul, ← QuotientGroup.mk_pow, hs1,
      QuotientGroup.mk_one]
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
  refine ⟨(y * s) ^ 2 ^ k, hmem, ?_⟩
  rw [map_pow]
  rfl

end CFSG.Quasithin.H13.NQCore
