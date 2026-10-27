module

public import CFSG.LocalAnalysis.StandardType.GGD5Defs
public import CFSG.LocalAnalysis.StandardType.GGD5Inputs

import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

@[expose] def lup10d_fr_Real {G : Type} [Group G] {Bs : Subgroup G} {x y : G} {L H : Subgroup G}
    (M : GGQTwoAmbModel 3 Bs x y L H) (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (ψ : MulAut ↥Bs) (m : lup10fa_Mat) : Prop :=
  ∀ v : M.V, κ (ggLin (p := 3) M.model ψ v) = m.mulVec (κ v)

theorem lup10d_fr_Real_mul {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) {ψ₁ ψ₂ : MulAut ↥Bs} {m₁ m₂ : lup10fa_Mat}
    (h₁ : lup10d_fr_Real M κ ψ₁ m₁) (h₂ : lup10d_fr_Real M κ ψ₂ m₂) :
    lup10d_fr_Real M κ (ψ₁ * ψ₂) (m₁ * m₂) := by
  intro v
  rw [map_mul, LinearEquiv.mul_apply, h₁, h₂, Matrix.mulVec_mulVec]

theorem lup10d_fr_Real_one {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) :
    lup10d_fr_Real M κ 1 1 := by
  intro v
  rw [map_one, Matrix.one_mulVec]
  rfl

theorem lup10d_fr_Real_unique {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) {ψ₁ ψ₂ : MulAut ↥Bs} {m : lup10fa_Mat}
    (h₁ : lup10d_fr_Real M κ ψ₁ m) (h₂ : lup10d_fr_Real M κ ψ₂ m) : ψ₁ = ψ₂ := by
  refine ggLin_injective (p := 3) M.model ?_
  refine LinearEquiv.ext fun v => κ.injective ?_
  rw [h₁, h₂]

theorem lup10d_fr_Real_inv {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) {ψ : MulAut ↥Bs} {m : lup10fa_Mat}
    (h : lup10d_fr_Real M κ ψ m) : lup10d_fr_Real M κ ψ⁻¹ m⁻¹ := by
  intro v
  have hmul : ∀ w : M.V,
      ggLin (p := 3) M.model ψ (ggLin (p := 3) M.model ψ⁻¹ w) = w := by
    intro w
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hdet : IsUnit m.det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
    intro u
    refine ⟨κ (ggLin (p := 3) M.model ψ⁻¹ (κ.symm u)), ?_⟩
    rw [← h (ggLin (p := 3) M.model ψ⁻¹ (κ.symm u)), hmul,
      LinearEquiv.apply_symm_apply]
  have hinv : m⁻¹ * m = 1 := Matrix.nonsing_inv_mul m hdet
  have hv : m.mulVec (κ (ggLin (p := 3) M.model ψ⁻¹ v)) = κ v := by
    rw [← h (ggLin (p := 3) M.model ψ⁻¹ v), hmul]
  rw [← Matrix.one_mulVec (κ (ggLin (p := 3) M.model ψ⁻¹ v)), ← hinv,
    ← Matrix.mulVec_mulVec, hv]

theorem lup10d_fr_real_conjDer {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) {S : Subgroup (MulAut ↥Bs)}
    {gens seed : Set lup10fa_Mat}
    (hg : ∀ s ∈ gens, ∃ ψ ∈ S, lup10d_fr_Real M κ ψ s)
    (hs : ∀ r ∈ seed, ∃ ψ ∈ S, lup10d_fr_Real M κ ψ r) {r : lup10fa_Mat}
    (hr : lup10fa_ConjDer gens seed r) : ∃ ψ ∈ S, lup10d_fr_Real M κ ψ r := by
  induction hr with
  | base hr => exact hs _ hr
  | conj hmem _ _ ihP =>
      obtain ⟨ψs, hψsS, hψs⟩ := hg _ hmem
      obtain ⟨ψr, hψrS, hψr⟩ := ihP
      exact ⟨ψs * ψr * ψs, mul_mem (mul_mem hψsS hψrS) hψsS,
        lup10d_fr_Real_mul M κ (lup10d_fr_Real_mul M κ hψs hψr) hψs⟩

theorem lup10d_fr_fix_zero : ∀ v : Fin 5 → ZMod 3,
    (lup10fa_s 1).mulVec v = v → (lup10fa_s 2).mulVec v = v →
    (lup10fa_s 3).mulVec v = v →
    v = v 0 • lup10fa_x + (v 0 + v 1) • ![0, 1, 2, 0, 2] := by
  decide +kernel

theorem lup10d_fr_fix_two : ∀ v : Fin 5 → ZMod 3,
    (lup10fa_s 0).mulVec v = v → (lup10fa_s 1).mulVec v = v →
    (lup10fa_s 3).mulVec v = v →
    v = v 0 • lup10fa_x + (v 2 + 2 * v 0) • ![0, 0, 1, 2, 1] := by
  decide +kernel

theorem lup10d_fr_fix_three : ∀ v : Fin 5 → ZMod 3,
    (lup10fa_s 0).mulVec v = v → (lup10fa_s 1).mulVec v = v →
    (lup10fa_s 2).mulVec v = v →
    v = v 0 • lup10fa_x + (v 4 + v 0) • ![0, 0, 0, 0, 1] := by
  decide +kernel

theorem lup10d_fr_fix_span {b0 : Fin 4} (hb0 : b0 ≠ 1) {v w : lup10fa_Vec}
    (hv : ∀ j : Fin 4, j ≠ b0 → (lup10fa_s j.castSucc).mulVec v = v)
    (hw : ∀ j : Fin 4, j ≠ b0 → (lup10fa_s j.castSucc).mulVec w = w)
    (hw0 : w ∉ Submodule.span (ZMod 3) {lup10fa_x}) :
    ∃ a c : ZMod 3, v = a • lup10fa_x + c • w := by
  have combine : ∀ (u : lup10fa_Vec) (a1 c1 a2 c2 : ZMod 3),
      v = a1 • lup10fa_x + c1 • u → w = a2 • lup10fa_x + c2 • u → c2 ≠ 0 →
      ∃ a c : ZMod 3, v = a • lup10fa_x + c • w := by
    intro u a1 c1 a2 c2 hv' hw' hc2
    refine ⟨a1 - c1 * c2⁻¹ * a2, c1 * c2⁻¹, ?_⟩
    rw [hv', hw', smul_add, smul_smul, smul_smul]
    have hc : c1 * c2⁻¹ * c2 = c1 := by
      rw [mul_assoc, inv_mul_cancel₀ hc2, mul_one]
    rw [hc]
    module
  fin_cases b0
  · have h1 := lup10d_fr_fix_zero v (hv 1 (by decide)) (hv 2 (by decide))
      (hv 3 (by decide))
    have h2 := lup10d_fr_fix_zero w (hw 1 (by decide)) (hw 2 (by decide))
      (hw 3 (by decide))
    refine combine _ (v 0) (v 0 + v 1) (w 0) (w 0 + w 1) h1 h2 ?_
    intro hc
    apply hw0
    rw [h2, hc, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact absurd rfl hb0
  · have h1 := lup10d_fr_fix_two v (hv 0 (by decide)) (hv 1 (by decide))
      (hv 3 (by decide))
    have h2 := lup10d_fr_fix_two w (hw 0 (by decide)) (hw 1 (by decide))
      (hw 3 (by decide))
    refine combine _ (v 0) (v 2 + 2 * v 0) (w 0) (w 2 + 2 * w 0) h1 h2 ?_
    intro hc
    apply hw0
    rw [h2, hc, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · have h1 := lup10d_fr_fix_three v (hv 0 (by decide)) (hv 1 (by decide))
      (hv 2 (by decide))
    have h2 := lup10d_fr_fix_three w (hw 0 (by decide)) (hw 1 (by decide))
      (hw 2 (by decide))
    refine combine _ (v 0) (v 4 + v 0) (w 0) (w 4 + w 0) h1 h2 ?_
    intro hc
    apply hw0
    rw [h2, hc, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem lup10d_fr_tau_four : lup10ab_tau (4 : Fin 5) = 0 := by
  decide +kernel

theorem lup10d_fr_tau_ne_zero : ∀ j : Fin 4, lup10ab_tau j.castSucc ≠ 0 := by
  decide +kernel

theorem lup10d_fr_tau_inj :
    ∀ i j : Fin 4, i ≠ j → lup10ab_tau i.castSucc ≠ lup10ab_tau j.castSucc := by
  decide +kernel

@[expose] noncomputable def lup10d_fr_zb {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) (z : lup10fa_Vec) : ↥Bs :=
  Additive.toMul (M.model.symm (κ.symm z))

theorem lup10d_fr_zb_model {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) (z : lup10fa_Vec) :
    M.model (Additive.ofMul (lup10d_fr_zb M κ z)) = κ.symm z := by
  simp [lup10d_fr_zb]

theorem lup10d_fr_model_mul {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (b₁ b₂ : ↥Bs) :
    M.model (Additive.ofMul (b₁ * b₂)) =
      M.model (Additive.ofMul b₁) + M.model (Additive.ofMul b₂) := by
  rw [ofMul_mul, map_add]

theorem lup10d_fr_model_pow {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (b : ↥Bs) (n : ℕ) :
    M.model (Additive.ofMul (b ^ n)) = n • M.model (Additive.ofMul b) := by
  rw [ofMul_pow, map_nsmul]

theorem lup10d_fr_smul_model {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (b : ↥Bs) (t : ZMod 3) :
    t • M.model (Additive.ofMul b) = M.model (Additive.ofMul (b ^ t.val)) := by
  rw [show t • M.model (Additive.ofMul b) =
      (t.val : ZMod 3) • M.model (Additive.ofMul b) from by rw [ZMod.natCast_zmod_val],
    Nat.cast_smul_eq_nsmul, lup10d_fr_model_pow]

theorem lup10d_fr_simple_mem {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (hLH : L ≤ H) (k : M.ι) :
    M.simple k ∈ ggAutomizer H Bs := by
  by_cases hk : k = M.a
  · subst hk
    exact M.simple_a_mem
  · refine ggAutomizer_mono Bs hLH ?_
    rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem lup10d_fr_yV_fixed {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκs : ∀ (i : Fin 5) (v : M.V),
      κ (ggLin (p := 3) M.model (M.simple (e (lup10ab_tau i))) v) = (lup10fa_s i).mulVec (κ v))
    (he0 : M.a = e 0) {b0 : Fin 4} (hb0 : e (lup10ab_tau b0.castSucc) = M.b) :
    ∀ j : Fin 4, j ≠ b0 → (lup10fa_s j.castSucc).mulVec (κ M.yV) = κ M.yV := by
  intro j hj
  have hk1 : e (lup10ab_tau j.castSucc) ≠ M.a := by
    intro h
    exact lup10d_fr_tau_ne_zero j (e.injective (h.trans he0))
  have hk2 : e (lup10ab_tau j.castSucc) ≠ M.b := by
    intro h
    exact lup10d_fr_tau_inj j b0 hj (e.injective (h.trans hb0.symm))
  have h := hκs j.castSucc M.yV
  rw [show M.yV = M.model (Additive.ofMul ⟨y, M.hy⟩) from rfl, ggLin_apply_ofMul,
    M.y_fixed_J _ hk1 hk2] at h
  exact h.symm

theorem lup10d_fr_yV_not_mem_span {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {x y : G} {L H D : Subgroup G}
    (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκx : ∃ ν : ZMod 3, ν ≠ 0 ∧ κ M.xV = ν • lup10fa_x) (hxp : x ^ 3 = 1)
    (hD : D = Subgroup.closure {x, y}) (hD9 : Nat.card ↥D = 9) :
    κ M.yV ∉ Submodule.span (ZMod 3) {lup10fa_x} := by
  intro hspan
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hspan
  obtain ⟨ν, hν0, hνx⟩ := hκx
  have hx0 : lup10fa_x = ν⁻¹ • κ M.xV := by
    rw [hνx, smul_smul, inv_mul_cancel₀ hν0, one_smul]
  have hky : κ M.yV = (t * ν⁻¹) • κ M.xV := by
    rw [← ht, hx0, smul_smul]
  have hky' : M.yV = (t * ν⁻¹) • M.xV := by
    apply κ.injective
    rw [hky, map_smul]
  have hyx : y = x ^ (t * ν⁻¹).val := by
    have h1 : M.model (Additive.ofMul ⟨y, M.hy⟩) =
        M.model (Additive.ofMul ((⟨x, M.hx⟩ : ↥Bs) ^ (t * ν⁻¹).val)) := by
      rw [show M.model (Additive.ofMul ⟨y, M.hy⟩) = M.yV from rfl, hky',
        show M.xV = M.model (Additive.ofMul ⟨x, M.hx⟩) from rfl,
        lup10d_fr_smul_model M ⟨x, M.hx⟩ (t * ν⁻¹)]
    have h2 : (⟨y, M.hy⟩ : ↥Bs) = ⟨x, M.hx⟩ ^ (t * ν⁻¹).val :=
      Additive.ofMul.injective (M.model.injective h1)
    exact congrArg Subtype.val h2
  have hy : y ∈ Subgroup.zpowers x :=
    Subgroup.mem_zpowers_iff.mpr ⟨((t * ν⁻¹).val : ℤ), by
      rw [zpow_natCast]
      exact hyx.symm⟩
  have hxmem : x ∈ Subgroup.zpowers x :=
    Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  have hDle : D ≤ Subgroup.zpowers x := by
    rw [hD]
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    rcases hg with rfl | rfl
    · exact hxmem
    · rw [hyx]
      exact Subgroup.pow_mem _ hxmem _
  have hle := Subgroup.card_le_of_le hDle
  rw [Nat.card_zpowers] at hle
  rw [hD9] at hle
  have hord : orderOf x ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hxp
  omega

theorem lup10d_fr_zB_mem_D {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {x y : G} {L H D : Subgroup G}
    (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκx : ∃ ν : ZMod 3, ν ≠ 0 ∧ κ M.xV = ν • lup10fa_x)
    {b0 : Fin 4} (hb0ne : b0 ≠ 1)
    (hyfix : ∀ j : Fin 4, j ≠ b0 → (lup10fa_s j.castSucc).mulVec (κ M.yV) = κ M.yV)
    (hyVspan : κ M.yV ∉ Submodule.span (ZMod 3) {lup10fa_x})
    {z : lup10fa_Vec}
    (hzfix : ∀ j : Fin 4, j ≠ b0 → (lup10fa_s j.castSucc).mulVec z = z)
    (hxD : x ∈ D) (hyD : y ∈ D) :
    (lup10d_fr_zb M κ z : G) ∈ D := by
  obtain ⟨a, c, hzc⟩ := lup10d_fr_fix_span hb0ne hzfix hyfix hyVspan
  obtain ⟨ν, hν0, hνx⟩ := hκx
  have hx0 : κ.symm lup10fa_x = ν⁻¹ • M.xV := by
    have h := congrArg κ.symm hνx
    rw [LinearEquiv.symm_apply_apply, map_smul] at h
    rw [h, smul_smul, inv_mul_cancel₀ hν0, one_smul]
  have hz : κ.symm z = (a * ν⁻¹) • M.xV + c • M.yV := by
    rw [hzc, map_add, map_smul, map_smul, LinearEquiv.symm_apply_apply]
    congr 1
    rw [hx0, smul_smul]
  have hmodel : M.model (Additive.ofMul (lup10d_fr_zb M κ z)) =
      M.model (Additive.ofMul ((⟨x, M.hx⟩ : ↥Bs) ^ (a * ν⁻¹).val *
        (⟨y, M.hy⟩ : ↥Bs) ^ c.val)) := by
    calc M.model (Additive.ofMul (lup10d_fr_zb M κ z))
        = (a * ν⁻¹) • M.xV + c • M.yV := by
          rw [lup10d_fr_zb_model M κ z, hz]
      _ = M.model (Additive.ofMul ((⟨x, M.hx⟩ : ↥Bs) ^ (a * ν⁻¹).val)) +
          M.model (Additive.ofMul ((⟨y, M.hy⟩ : ↥Bs) ^ c.val)) := by
          rw [show M.xV = M.model (Additive.ofMul ⟨x, M.hx⟩) from rfl,
            show M.yV = M.model (Additive.ofMul ⟨y, M.hy⟩) from rfl,
            lup10d_fr_smul_model M ⟨x, M.hx⟩ (a * ν⁻¹),
            lup10d_fr_smul_model M ⟨y, M.hy⟩ c]
      _ = M.model (Additive.ofMul ((⟨x, M.hx⟩ : ↥Bs) ^ (a * ν⁻¹).val *
          (⟨y, M.hy⟩ : ↥Bs) ^ c.val)) := by
          rw [lup10d_fr_model_mul M]
  have hzb_eq : lup10d_fr_zb M κ z = (⟨x, M.hx⟩ : ↥Bs) ^ (a * ν⁻¹).val *
      (⟨y, M.hy⟩ : ↥Bs) ^ c.val :=
    Additive.ofMul.injective (M.model.injective hmodel)
  have hcoe : ((lup10d_fr_zb M κ z : ↥Bs) : G) =
      x ^ (a * ν⁻¹).val * y ^ c.val := by
    rw [hzb_eq, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
  rw [hcoe]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hxD _) (Subgroup.pow_mem _ hyD _)

theorem lup10d_fr_zB_not_mem_zpowers {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκx : ∃ ν : ZMod 3, ν ≠ 0 ∧ κ M.xV = ν • lup10fa_x)
    {z : lup10fa_Vec} (hzspan : z ∉ Submodule.span (ZMod 3) {lup10fa_x}) :
    (lup10d_fr_zb M κ z : G) ∉ Subgroup.zpowers x := by
  intro hmem
  rw [Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨n, hn⟩ := hmem
  have hn' : (⟨x, M.hx⟩ : ↥Bs) ^ n = lup10d_fr_zb M κ z := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hn
  obtain ⟨ν, -, hνx⟩ := hκx
  have h1 : M.model (Additive.ofMul ((⟨x, M.hx⟩ : ↥Bs) ^ n)) = n • M.xV := by
    rw [ofMul_zpow, map_zsmul]
    rfl
  have h2 : κ.symm z = n • M.xV := by
    rw [← lup10d_fr_zb_model M κ z, ← hn', h1]
  have h3 : z = κ (n • M.xV) := by
    rw [← h2, LinearEquiv.apply_symm_apply]
  apply hzspan
  rw [h3, map_zsmul, hνx, ← Int.cast_smul_eq_zsmul (ZMod 3)]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (Submodule.mem_span_singleton_self _))

theorem lup10d_fr_zB_ne_one {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    {z : lup10fa_Vec} (hzspan : z ∉ Submodule.span (ZMod 3) {lup10fa_x}) :
    (lup10d_fr_zb M κ z : G) ≠ 1 := by
  intro h
  apply hzspan
  have h1 : κ.symm z = 0 := by
    have hb1 : lup10d_fr_zb M κ z = 1 := Subtype.ext h
    rw [← lup10d_fr_zb_model M κ z, hb1,
      show Additive.ofMul (1 : ↥Bs) = 0 from rfl, map_zero]
  have h2 : z = 0 := by
    have h3 := congrArg κ h1
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h3
  rw [h2]
  exact Submodule.zero_mem _

theorem lup10d_fr_x_not_zpowers_zB {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x y : G} {L H : Subgroup G}
    (hB : GGBstar 3 B Bs) (hx1 : x ≠ 1)
    (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) {z : lup10fa_Vec}
    (hzbnot : (lup10d_fr_zb M κ z : G) ∉ Subgroup.zpowers x) :
    x ∉ Subgroup.zpowers (lup10d_fr_zb M κ z : G) := by
  intro hmem
  exact hzbnot (mem_zpowers_of_mem_zpowers_of_ne_one Nat.prime_three
    (hB.2.1.2 _ (lup10d_fr_zb M κ z).2) hmem hx1)

theorem lup10d_fr_S0_real {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκs : ∀ (i : Fin 5) (v : M.V),
      κ (ggLin (p := 3) M.model (M.simple (e (lup10ab_tau i))) v) = (lup10fa_s i).mulVec (κ v))
    (hmem : ∀ k : M.ι, M.simple k ∈ ggAutomizer H Bs) :
    ∀ r ∈ lup10fa_S0, ∃ ψ ∈ ggAutomizer H Bs, lup10d_fr_Real M κ ψ r := by
  have hgen : ∀ s ∈ Set.range lup10fa_s, ∃ ψ ∈ ggAutomizer H Bs, lup10d_fr_Real M κ ψ s := by
    intro s hs
    obtain ⟨i, rfl⟩ := hs
    exact ⟨M.simple (e (lup10ab_tau i)), hmem _, hκs i⟩
  intro r hr
  exact lup10d_fr_real_conjDer M κ hgen hgen hr

theorem lup10d_fr_WJ_real {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {x y : G}
    {L J H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκs : ∀ (i : Fin 5) (v : M.V),
      κ (ggLin (p := 3) M.model (M.simple (e (lup10ab_tau i))) v) = (lup10fa_s i).mulVec (κ v))
    (he0 : M.a = e 0)
    (hAJ : ggAutomizer J Bs =
      Subgroup.closure (M.simple '' {k : M.ι | k ≠ M.a ∧ k ≠ M.b})) {b0 : Fin 4}
    (hb0 : e (lup10ab_tau b0.castSucc) = M.b) :
    ∀ r ∈ lup10fa_WJ b0, ∃ ψ ∈ ggAutomizer J Bs, lup10d_fr_Real M κ ψ r := by
  have hgen : ∀ s ∈ lup10fa_wjg b0, ∃ ψ ∈ ggAutomizer J Bs, lup10d_fr_Real M κ ψ s := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := hs
    have hk1 : e (lup10ab_tau j.castSucc) ≠ M.a := by
      intro h
      exact lup10d_fr_tau_ne_zero j (e.injective (h.trans he0))
    have hk2 : e (lup10ab_tau j.castSucc) ≠ M.b := by
      intro h
      exact lup10d_fr_tau_inj j b0 hj (e.injective (h.trans hb0.symm))
    refine ⟨M.simple (e (lup10ab_tau j.castSucc)), ?_, hκs j.castSucc⟩
    rw [hAJ]
    exact Subgroup.subset_closure ⟨_, ⟨hk1, hk2⟩, rfl⟩
  intro r hr
  exact lup10d_fr_real_conjDer M κ hgen hgen hr

theorem lup10d_fr_Sp_real {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκs : ∀ (i : Fin 5) (v : M.V),
      κ (ggLin (p := 3) M.model (M.simple (e (lup10ab_tau i))) v) = (lup10fa_s i).mulVec (κ v))
    (he0 : M.a = e 0) (hgen : ∀ k : M.ι, M.simple k ∈ ggAutomizer ⊤ Bs)
    {γ : Equiv.Perm (Fin 4)} {lam c' : ZMod 3} {w' φ : MulAut ↥Bs}
    (hw' : w' ∈ ggAutomizer ⊤ Bs) (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hform : ∀ v : M.V, κ (ggLin (p := 3) M.model (w'⁻¹ * φ) v) =
      (lup10fa_twist γ lam c').mulVec (κ v)) :
    ∀ r ∈ lup10fa_Sp γ lam c', ∃ ψ ∈ ggAutomizer ⊤ Bs, lup10d_fr_Real M κ ψ r := by
  have h4 : lup10d_fr_Real M κ (M.simple M.a) (lup10fa_s 4) := by
    have h := hκs (4 : Fin 5)
    have he4 : e (lup10ab_tau (4 : Fin 5)) = M.a := by
      rw [lup10d_fr_tau_four]
      exact he0.symm
    rwa [he4] at h
  set χ : MulAut ↥Bs := (w'⁻¹ * φ) * M.simple M.a * (w'⁻¹ * φ)⁻¹ with hχdef
  have hχ_top : χ ∈ ggAutomizer ⊤ Bs := by
    rw [hχdef]
    exact mul_mem (mul_mem (mul_mem (Subgroup.inv_mem _ hw') hφ) (hgen M.a))
      (Subgroup.inv_mem _ (mul_mem (Subgroup.inv_mem _ hw') hφ))
  have hχ_real : lup10d_fr_Real M κ χ
      (lup10fa_twist γ lam c' * lup10fa_s 4 * (lup10fa_twist γ lam c')⁻¹) := by
    rw [hχdef]
    exact lup10d_fr_Real_mul M κ (lup10d_fr_Real_mul M κ hform h4)
      (lup10d_fr_Real_inv M κ hform)
  have hgen' : ∀ s ∈ lup10fa_gens γ lam c', ∃ ψ ∈ ggAutomizer ⊤ Bs,
      lup10d_fr_Real M κ ψ s := by
    intro s hs
    rcases hs with hs | hs
    · obtain ⟨i, rfl⟩ := hs
      exact ⟨M.simple (e (lup10ab_tau i)), hgen _, hκs i⟩
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact ⟨χ, hχ_top, hχ_real⟩
  intro r hr
  exact lup10d_fr_real_conjDer M κ hgen' hgen' hr

theorem lup10d_fr_O_real {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hLB : GGLBalanceInput) (hI : GGThmIHyp 3 B x L) (hB : GGBstar 3 B Bs)
    (hDJ : LargeEvenStdSub 3 B x L D J) (hnb : GGNbr 3 B x D J y K)
    (M : GGQTwoAmbModel 3 Bs x y L (L ⊔ K)) (e : Fin 5 ≃ M.ι)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκs : ∀ (i : Fin 5) (v : M.V),
      κ (ggLin (p := 3) M.model (M.simple (e (lup10ab_tau i))) v) = (lup10fa_s i).mulVec (κ v))
    (hκx : ∃ ν : ZMod 3, ν ≠ 0 ∧ κ M.xV = ν • lup10fa_x)
    (hLab : lup10d_LabelData 3 Bs x L J M) (hSC : lup10d_SCData Bs J)
    (he0 : M.a = e 0) {b0 : Fin 4} {γ : Equiv.Perm (Fin 4)} {lam c' : ZMod 3}
    (hadm : lup10fa_Adm b0 γ lam c') (hb0 : e (lup10ab_tau b0.castSucc) = M.b)
    (hWJreal : ∀ r ∈ lup10fa_WJ b0, ∃ ψ ∈ ggAutomizer J Bs, lup10d_fr_Real M κ ψ r)
    (hSpreal : ∀ r ∈ lup10fa_Sp γ lam c',
      ∃ ψ ∈ ggAutomizer ⊤ Bs, lup10d_fr_Real M κ ψ r)
    {z : lup10fa_Vec}
    (hzfix : ∀ j : Fin 4, j ≠ b0 → (lup10fa_s j.castSucc).mulVec z = z)
    (hzspan : z ∉ Submodule.span (ZMod 3) {lup10fa_x})
    (hzO : ∀ v : lup10fa_Vec, (∀ r ∈ lup10fa_O b0 γ lam c' z, r.mulVec v = v) →
      v ∈ Submodule.span (ZMod 3) {z}) :
    ∀ r ∈ lup10fa_O b0 γ lam c' z,
      ∃ ψ ∈ ggAutomizer (ggG0 3 B x L D J) Bs, lup10d_fr_Real M κ ψ r := by
  have hb0ne : b0 ≠ 1 := by
    intro h
    apply hadm.2.2.1
    rw [h, hadm.1]
  have hxp : x ^ 3 = 1 := hB.2.1.2 x M.hx
  have hx1 : x ≠ 1 := hI.2.2.2.2.2.2.1.2.2.1
  have hBmax : LargeEvenIsBmax 3 B := hI.2.2.2.2.2.2.1.1
  have hxB : x ∈ B := hI.2.2.2.2.2.2.1.2.1
  have hyfix : ∀ j : Fin 4, j ≠ b0 → (lup10fa_s j.castSucc).mulVec (κ M.yV) = κ M.yV :=
    lup10d_fr_yV_fixed M e κ hκs he0 hb0
  have hD9 : Nat.card ↥D = 9 := by
    rw [hDJ.1.2.2.1]
    norm_num
  have hxD : x ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (by simp)
  have hyD : y ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (by simp)
  have hyVspan : κ M.yV ∉ Submodule.span (ZMod 3) {lup10fa_x} :=
    lup10d_fr_yV_not_mem_span M κ hκx hxp hnb.2.1 hD9
  have hzD : (lup10d_fr_zb M κ z : G) ∈ D :=
    lup10d_fr_zB_mem_D M κ hκx hb0ne hyfix hyVspan hzfix hxD hyD
  have hzbnot : (lup10d_fr_zb M κ z : G) ∉ Subgroup.zpowers x :=
    lup10d_fr_zB_not_mem_zpowers M κ hκx hzspan
  have hzb1 : (lup10d_fr_zb M κ z : G) ≠ 1 :=
    lup10d_fr_zB_ne_one M κ hzspan
  have hxz : x ∉ Subgroup.zpowers (lup10d_fr_zb M κ z : G) :=
    lup10d_fr_x_not_zpowers_zB hB hx1 M κ hzbnot
  have hzB : (lup10d_fr_zb M κ z : G) ∈ Bs := hB.1 (hDJ.1.1 hzD)
  have hDz : D = Subgroup.closure {x, (lup10d_fr_zb M κ z : G)} :=
    eq_closure_pair_of_mem hI hDJ hzD hzbnot
  obtain ⟨X, hX, hJX, -⟩ := exists_pComponent_of_stdSub
    (ggPumpupInput_of_lBalance hLB) hI hDJ hLab.1 hzD hzb1
  have hcardBs : Nat.card ↥Bs = 3 ^ 5 := by
    have h1 : Nat.card ↥Bs = Nat.card M.V :=
      Nat.card_congr (Additive.ofMul.trans M.model.toEquiv)
    have h2 : Nat.card M.V = Nat.card (Fin 5 → ZMod 3) := Nat.card_congr κ.toEquiv
    rw [h1, h2, Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card, Nat.card_fin]
  have hlogBs : Nat.log 3 (Nat.card ↥Bs) = 5 := by
    rw [hcardBs, Nat.log_pow (by norm_num : 1 < 3)]
  have hcardJ : Nat.card ↥(Bs ⊓ J) = 3 ^ 3 := by
    rw [hSC.2.2]
    norm_num
  have hlogJ : Nat.log 3 (Nat.card ↥(Bs ⊓ J)) = 3 := by
    rw [hcardJ, Nat.log_pow (by norm_num : 1 < 3)]
  have hrank : Nat.log 3 (Nat.card ↥Bs) < 2 * Nat.log 3 (Nat.card ↥(Bs ⊓ J)) := by
    rw [hlogBs, hlogJ]
    norm_num
  have hN := normalizer_inf_le_normalizer_of_pComponent_of_coprime_center
    (p := 3) (H := Subgroup.centralizer ({(lup10d_fr_zb M κ z : G)} : Set G))
    (X := X) (J := J) (E := Bs) hX hJX hB.2.1 hLab.2.1 hrank
  let R : Set (MulAut ↥Bs) :=
    {ψ | ψ ∈ ggAutomizer ⊤ Bs ∧ ψ ⟨(lup10d_fr_zb M κ z : G), hzB⟩ = ⟨_, hzB⟩}
  let S : Set (MulAut ↥Bs) := (ggAutomizer J Bs : Set (MulAut ↥Bs))
  have horb := ggAutomizer_orbit_le_of_normalizer_le (z := (lup10d_fr_zb M κ z : G)) hzB
    hX.1 hJX hN (R := R) (S := S) (fun r hr => hr) (fun s hs => hs)
  have horbit : ∀ r ∈ lup10fa_O b0 γ lam c' z,
      ∃ ρ ∈ Subgroup.closure R, ∃ s ∈ (ggAutomizer J Bs : Set (MulAut ↥Bs)),
        lup10d_fr_Real M κ (ρ * s * ρ⁻¹) r := by
    intro r hr
    induction hr with
    | base hrs =>
        obtain ⟨ψ, hψ, hψr⟩ := hWJreal _ hrs
        exact ⟨1, Subgroup.one_mem _, ψ, hψ, by simpa using hψr⟩
    | conj hmem hsq _ ihP =>
        obtain ⟨ψt, hψt_top, hψt⟩ := hSpreal _ hmem.1
        have hψtfix : ψt ⟨(lup10d_fr_zb M κ z : G), hzB⟩ = ⟨_, hzB⟩ := by
          apply (ggLin_fix_iff (p := 3) M.model ψt
            ⟨(lup10d_fr_zb M κ z : G), hzB⟩).mpr
          rw [lup10d_fr_zb_model M κ z]
          apply κ.injective
          rw [hψt (κ.symm z), LinearEquiv.apply_symm_apply, hmem.2]
        have hψt2 : ψt * ψt = 1 := by
          have h2 : lup10d_fr_Real M κ (ψt * ψt) 1 := by
            have h := lup10d_fr_Real_mul M κ hψt hψt
            rwa [hsq] at h
          exact lup10d_fr_Real_unique M κ h2 (lup10d_fr_Real_one M κ)
        have hψtinv : ψt⁻¹ = ψt := inv_eq_of_mul_eq_one_left hψt2
        have hψtR : ψt ∈ R := ⟨hψt_top, hψtfix⟩
        obtain ⟨ρ, hρ, sJ, hsJ, hReal⟩ := ihP
        refine ⟨ψt * ρ, Subgroup.mul_mem _ (Subgroup.subset_closure hψtR) hρ, sJ, hsJ, ?_⟩
        have heq : (ψt * ρ) * sJ * (ψt * ρ)⁻¹ = ψt * (ρ * sJ * ρ⁻¹) * ψt := by
          rw [mul_inv_rev, hψtinv]
          group
        rw [heq]
        exact lup10d_fr_Real_mul M κ (lup10d_fr_Real_mul M κ hψt hReal) hψt
  have horbX : ∀ r ∈ lup10fa_O b0 γ lam c' z,
      ∃ ψ ∈ ggAutomizer X Bs, lup10d_fr_Real M κ ψ r := by
    intro r hr
    obtain ⟨ρ, hρ, sJ, hsJ, hReal⟩ := horbit r hr
    exact ⟨ρ * sJ * ρ⁻¹, horb.1 ⟨ρ, hρ, sJ, hsJ, rfl⟩, hReal⟩
  have hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) →
      (b : G) ∈ Subgroup.zpowers (lup10d_fr_zb M κ z : G) := by
    intro b hb
    have hvO : ∀ r ∈ lup10fa_O b0 γ lam c' z,
        r.mulVec (κ (M.model (Additive.ofMul b))) = κ (M.model (Additive.ofMul b)) := by
      intro r hr
      obtain ⟨ψ, hψX, hψr⟩ := horbX r hr
      have hfixb : ggLin (p := 3) M.model ψ (M.model (Additive.ofMul b)) =
          M.model (Additive.ofMul b) :=
        (ggLin_fix_iff (p := 3) M.model ψ b).mp (hb ψ hψX)
      rw [← hψr (M.model (Additive.ofMul b)), hfixb]
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hzO _ hvO)
    have hmodel : M.model (Additive.ofMul b) =
        t • M.model (Additive.ofMul (lup10d_fr_zb M κ z)) := by
      apply κ.injective
      rw [map_smul, lup10d_fr_zb_model M κ z, LinearEquiv.apply_symm_apply, ← ht]
    rw [lup10d_fr_smul_model M (lup10d_fr_zb M κ z) t] at hmodel
    have hb_eq : b = lup10d_fr_zb M κ z ^ t.val :=
      Additive.ofMul.injective (M.model.injective hmodel)
    have hbG : (b : G) = ((lup10d_fr_zb M κ z : ↥Bs) : G) ^ t.val := by
      rw [hb_eq, Subgroup.coe_pow]
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨(t.val : ℤ), by rw [zpow_natCast]; exact hbG.symm⟩
  have hXG : X ≤ ggG0 3 B x L D J :=
    le_ggG0_of_ggAutomizer_fixed_le_zpowers hBmax hB hxB (hDJ.1.1 hzD) hzb1 hxz hDz hDJ hX
      hJX hLab.1 hfix
  intro r hr
  obtain ⟨ψ, hψX, hψr⟩ := horbX r hr
  exact ⟨ψ, ggAutomizer_mono Bs hXG hψX, hψr⟩

theorem lup10d_forced_reflection {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G}
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (h5 : GGQTwoCentralizerInput)
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) (hxL : x ∉ L)
    (hrow : ¬ ∃ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K ∧
      ((GGQTwoTwoNodeRowAt 3 L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt 3 K J ∧ y ∉ K)))
    (hno : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ¬ Nonempty (GGQTwoModel 3 Bs x y D L J K))
    {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (M : GGQTwoAmbModel 3 Bs x y L (L ⊔ K)) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hV : Submodule.span (ZMod 3)
      (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤)
    (hbas : M.toLin.Basis) (hLab : lup10d_LabelData 3 Bs x L J M) (hSC : lup10d_SCData Bs J)
    (hTF : lup10fa_TwistFacts)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκ1 : ∀ i : Fin 5, κ (M.coroot (e (lup10ab_tau i))) = Pi.single i 1)
    (hκs : ∀ (i : Fin 5) (v : M.V),
      κ (ggLin (p := 3) M.model (M.simple (e (lup10ab_tau i))) v) = (lup10fa_s i).mulVec (κ v))
    (hκx : ∃ ν : ZMod 3, ν ≠ 0 ∧ κ M.xV = ν • lup10fa_x)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs) (w' : MulAut ↥Bs)
    (hw'L : w' ∈ ggAutomizer L Bs) (b0 : Fin 4) (γ : Equiv.Perm (Fin 4)) (lam c' : ZMod 3)
    (hadm : lup10fa_Adm b0 γ lam c') (hb0 : e (lup10ab_tau b0.castSucc) = M.b)
    (hform : ∀ v : M.V, κ (ggLin (p := 3) M.model (w'⁻¹ * φ) v) =
      (lup10fa_twist γ lam c').mulVec (κ v)) :
    ∃ r' : MulAut ↥Bs, r' ∈ ggAutomizer (ggG0 3 B x L D J) Bs ∧
      ggLin (p := 3) M.model r' = ggLin (p := 3) M.model (φ * M.simple M.a * φ⁻¹) := by
  classical
  have _ : GGQTwoCentralizerInput := h5
  have _ : GGStdSubPrimeInput := hP
  have _ : GGQTwoI1 Bs D J := hI1
  have _ : x ∉ L := hxL
  have _ := hrow
  have _ := hno
  have _ := hecart
  have _ := hV
  have _ := hbas
  have _ := hκ1
  have hI : GGThmIHyp 3 B x L := hS.1.1.1
  have hB : GGBstar 3 B Bs := hS.1.1.2.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hLKleG0 : L ⊔ K ≤ ggG0 3 B x L D J :=
    sup_le (le_ggG0_left 3 B x L D J) (le_ggG0_of_ggNbr hnb)
  have hsimple : ∀ k : M.ι, M.simple k ∈ ggAutomizer (L ⊔ K) Bs :=
    lup10d_fr_simple_mem M le_sup_left
  have hgenmem : ∀ k : M.ι, M.simple k ∈ ggAutomizer ⊤ Bs :=
    fun k => ggAutomizer_mono Bs le_top (hsimple k)
  have hS0realLK : ∀ r ∈ lup10fa_S0,
      ∃ ψ ∈ ggAutomizer (L ⊔ K) Bs, lup10d_fr_Real M κ ψ r :=
    lup10d_fr_S0_real M e κ hκs hsimple
  have hS0real : ∀ r ∈ lup10fa_S0,
      ∃ ψ ∈ ggAutomizer (ggG0 3 B x L D J) Bs, lup10d_fr_Real M κ ψ r := by
    intro r hr
    obtain ⟨ψ, hψ, hreal⟩ := hS0realLK r hr
    exact ⟨ψ, ggAutomizer_mono Bs hLKleG0 hψ, hreal⟩
  have hWJreal : ∀ r ∈ lup10fa_WJ b0,
      ∃ ψ ∈ ggAutomizer J Bs, lup10d_fr_Real M κ ψ r :=
    lup10d_fr_WJ_real M e κ hκs he0 hLab.2.2.1 hb0
  have hw'LK : w' ∈ ggAutomizer (L ⊔ K) Bs :=
    ggAutomizer_mono (H := L) (H' := L ⊔ K) Bs le_sup_left hw'L
  have hw'top : w' ∈ ggAutomizer ⊤ Bs :=
    ggAutomizer_mono (H := L ⊔ K) (H' := ⊤) Bs le_top hw'LK
  have hSpreal : ∀ r ∈ lup10fa_Sp γ lam c',
      ∃ ψ ∈ ggAutomizer ⊤ Bs, lup10d_fr_Real M κ ψ r :=
    lup10d_fr_Sp_real M e κ hκs he0 hgenmem hw'top hφ hform
  obtain ⟨-, z₁, z₂, hz, hSp⟩ := hTF b0 γ lam c' hadm
  have hz₁ := hz z₁ (by simp)
  have hz₂ := hz z₂ (by simp)
  have hOreal₁ : ∀ r ∈ lup10fa_O b0 γ lam c' z₁,
      ∃ ψ ∈ ggAutomizer (ggG0 3 B x L D J) Bs, lup10d_fr_Real M κ ψ r :=
    lup10d_fr_O_real hLB hI hB hDJ hnb M e κ hκs hκx hLab hSC he0 hadm hb0
      hWJreal hSpreal hz₁.1 hz₁.2.1 hz₁.2.2
  have hOreal₂ : ∀ r ∈ lup10fa_O b0 γ lam c' z₂,
      ∃ ψ ∈ ggAutomizer (ggG0 3 B x L D J) Bs, lup10d_fr_Real M κ ψ r :=
    lup10d_fr_O_real hLB hI hB hDJ hnb M e κ hκs hκx hLab hSC he0 hadm hb0
      hWJreal hSpreal hz₂.1 hz₂.2.1 hz₂.2.2
  have hrSp : (lup10fa_twist γ lam c' * lup10fa_s 4 * (lup10fa_twist γ lam c')⁻¹) ∈
      lup10fa_Sp γ lam c' :=
    lup10fa_ConjDer.base (Set.mem_union_right _ rfl)
  have hconj := hSp hrSp
  have hmemO : ∀ s ∈ (lup10fa_S0 ∪ lup10fa_O b0 γ lam c' z₁ ∪
      lup10fa_O b0 γ lam c' z₂),
      ∃ ψ ∈ ggAutomizer (ggG0 3 B x L D J) Bs, lup10d_fr_Real M κ ψ s := by
    intro s hs
    rcases hs with (hs | hs) | hs
    · exact hS0real s hs
    · exact hOreal₁ s hs
    · exact hOreal₂ s hs
  obtain ⟨ψ₂, hψ₂G0, hψ₂real⟩ :=
    lup10d_fr_real_conjDer M κ hmemO hmemO hconj
  set χ : MulAut ↥Bs := (w'⁻¹ * φ) * M.simple M.a * (w'⁻¹ * φ)⁻¹ with hχdef
  have h4 : lup10d_fr_Real M κ (M.simple M.a) (lup10fa_s 4) := by
    have h := hκs (4 : Fin 5)
    have he4 : e (lup10ab_tau (4 : Fin 5)) = M.a := by
      rw [lup10d_fr_tau_four]
      exact he0.symm
    rwa [he4] at h
  have hχreal : lup10d_fr_Real M κ χ
      (lup10fa_twist γ lam c' * lup10fa_s 4 * (lup10fa_twist γ lam c')⁻¹) := by
    rw [hχdef]
    exact lup10d_fr_Real_mul M κ (lup10d_fr_Real_mul M κ hform h4)
      (lup10d_fr_Real_inv M κ hform)
  have huniq : χ = ψ₂ := lup10d_fr_Real_unique M κ hχreal hψ₂real
  have hχG0 : χ ∈ ggAutomizer (ggG0 3 B x L D J) Bs := by
    rw [huniq]
    exact hψ₂G0
  have hw'G0 : w' ∈ ggAutomizer (ggG0 3 B x L D J) Bs :=
    ggAutomizer_mono Bs (le_ggG0_left 3 B x L D J) hw'L
  have hmem : w' * χ * w'⁻¹ ∈ ggAutomizer (ggG0 3 B x L D J) Bs :=
    mul_mem (mul_mem hw'G0 hχG0) (Subgroup.inv_mem _ hw'G0)
  have heq : w' * χ * w'⁻¹ = φ * M.simple M.a * φ⁻¹ := by
    rw [hχdef]
    group
  exact ⟨φ * M.simple M.a * φ⁻¹, heq ▸ hmem, rfl⟩

theorem ggD5ForcedInput_holds : GGD5ForcedInput := by
  intro hTF hLB hP h5 G _ _ B Bs x L D J hS hI1 hxL hrow hno y K hnb M e hecart he0 hV hbas hLab
    hSC κ hκ1 hκs hκx φ hφ w' hw'L b0 γ lam c' hadm hb0 hform
  exact lup10d_forced_reflection hLB hP h5 hS hI1 hxL hrow hno hnb M e hecart he0 hV hbas hLab hSC
    hTF κ hκ1 hκs hκx hφ w' hw'L b0 γ lam c' hadm hb0 hform

end CFSG.StandardType

end
