module

public import CFSG.LocalAnalysis.StandardType.GGD5Defs
import CFSG.LocalAnalysis.StandardType.GGD5AbsCoord
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

private def lup10aj_s (i : Fin 4) : lup10fa_Mat := lup10fa_s i.castSucc

private def lup10aj_v (b : Fin 4) : lup10fa_Vec :=
  if b = 0 then ![0, 1, 2, 0, 2] else if b = 2 then ![0, 0, 1, 2, 1] else ![0, 0, 0, 0, 1]

private def lup10aj_rep0 : Fin 8 → lup10fa_Mat :=
  ![1, lup10aj_s 0, lup10aj_s 1 * lup10aj_s 0, lup10aj_s 2 * lup10aj_s 1 * lup10aj_s 0,
    lup10aj_s 3 * lup10aj_s 1 * lup10aj_s 0,
    lup10aj_s 3 * lup10aj_s 2 * lup10aj_s 1 * lup10aj_s 0,
    lup10aj_s 1 * lup10aj_s 3 * lup10aj_s 2 * lup10aj_s 1 * lup10aj_s 0,
    lup10aj_s 0 * lup10aj_s 1 * lup10aj_s 3 * lup10aj_s 2 * lup10aj_s 1 * lup10aj_s 0]

private def lup10aj_rep2 : Fin 8 → lup10fa_Mat :=
  ![1, lup10aj_s 2, lup10aj_s 1 * lup10aj_s 2, lup10aj_s 0 * lup10aj_s 1 * lup10aj_s 2,
    lup10aj_s 3 * lup10aj_s 1 * lup10aj_s 2,
    lup10aj_s 3 * lup10aj_s 0 * lup10aj_s 1 * lup10aj_s 2,
    lup10aj_s 1 * lup10aj_s 3 * lup10aj_s 0 * lup10aj_s 1 * lup10aj_s 2,
    lup10aj_s 2 * lup10aj_s 1 * lup10aj_s 3 * lup10aj_s 0 * lup10aj_s 1 * lup10aj_s 2]

private def lup10aj_rep3 : Fin 8 → lup10fa_Mat :=
  ![1, lup10aj_s 3, lup10aj_s 1 * lup10aj_s 3, lup10aj_s 0 * lup10aj_s 1 * lup10aj_s 3,
    lup10aj_s 2 * lup10aj_s 1 * lup10aj_s 3,
    lup10aj_s 2 * lup10aj_s 0 * lup10aj_s 1 * lup10aj_s 3,
    lup10aj_s 1 * lup10aj_s 2 * lup10aj_s 0 * lup10aj_s 1 * lup10aj_s 3,
    lup10aj_s 3 * lup10aj_s 1 * lup10aj_s 2 * lup10aj_s 0 * lup10aj_s 1 * lup10aj_s 3]

private def lup10aj_rep (b : Fin 4) : Fin 8 → lup10fa_Mat :=
  if b = 0 then lup10aj_rep0 else if b = 2 then lup10aj_rep2 else lup10aj_rep3

private def lup10aj_W : Submonoid lup10fa_Mat :=
  Submonoid.closure (Set.range lup10aj_s)

private def lup10aj_P (b : Fin 4) : Submonoid lup10fa_Mat :=
  Submonoid.closure (Set.range (fun j : {j : Fin 4 // j ≠ b} => lup10aj_s j.1))

private theorem lup10aj_rep_zero (b : Fin 4) (hb : b ≠ 1) : lup10aj_rep b 0 = 1 := by
  fin_cases b
  · rfl
  · exact absurd rfl hb
  · rfl
  · rfl

private theorem lup10aj_v_fixed (b : Fin 4) (hb : b ≠ 1) :
    ∀ j : Fin 4, j ≠ b → (lup10aj_s j).mulVec (lup10aj_v b) = lup10aj_v b := by
  fin_cases b
  · decide +kernel
  · exact absurd rfl hb
  · decide +kernel
  · decide +kernel

private theorem lup10aj_v_not_span (b : Fin 4) (hb : b ≠ 1) :
    ∀ t : ZMod 3, t • lup10fa_x ≠ lup10aj_v b := by
  fin_cases b
  · decide +kernel
  · exact absurd rfl hb
  · decide +kernel
  · decide +kernel

private theorem lup10aj_rep_orbit_inj (b : Fin 4) (hb : b ≠ 1) :
    ∀ u u' : Fin 8, (lup10aj_rep b u).mulVec (lup10aj_v b) =
      (lup10aj_rep b u').mulVec (lup10aj_v b) → u = u' := by
  fin_cases b
  · decide +kernel
  · exact absurd rfl hb
  · decide +kernel
  · decide +kernel

private theorem lup10aj_step (b : Fin 4) (hb : b ≠ 1) :
    ∀ (i : Fin 4) (u : Fin 8),
      (∃ u' : Fin 8, lup10aj_s i * lup10aj_rep b u = lup10aj_rep b u' ∧
        (lup10aj_rep b u').mulVec (lup10aj_v b) =
          (lup10aj_s i).mulVec ((lup10aj_rep b u).mulVec (lup10aj_v b))) ∨
      ∃ j : Fin 4, j ≠ b ∧ lup10aj_s i * lup10aj_rep b u =
        lup10aj_rep b u * lup10aj_s j := by
  fin_cases b
  · decide +kernel
  · exact absurd rfl hb
  · decide +kernel
  · decide +kernel

private theorem lup10aj_s_fix_x : ∀ j : Fin 4, (lup10aj_s j).mulVec lup10fa_x = lup10fa_x := by
  decide +kernel

private theorem lup10aj_fix_zero : ∀ v : Fin 5 → ZMod 3,
    (lup10aj_s 1).mulVec v = v → (lup10aj_s 2).mulVec v = v → (lup10aj_s 3).mulVec v = v →
    v = v 0 • lup10fa_x + (v 0 + v 1) • ![0, 1, 2, 0, 2] := by
  decide +kernel

private theorem lup10aj_fix_two : ∀ v : Fin 5 → ZMod 3,
    (lup10aj_s 0).mulVec v = v → (lup10aj_s 1).mulVec v = v → (lup10aj_s 3).mulVec v = v →
    v = v 0 • lup10fa_x + (v 2 + 2 * v 0) • ![0, 0, 1, 2, 1] := by
  decide +kernel

private theorem lup10aj_fix_three : ∀ v : Fin 5 → ZMod 3,
    (lup10aj_s 0).mulVec v = v → (lup10aj_s 1).mulVec v = v → (lup10aj_s 2).mulVec v = v →
    v = v 0 • lup10fa_x + (v 4 + v 0) • ![0, 0, 0, 0, 1] := by
  decide +kernel

private theorem lup10aj_fix_span {b0 : Fin 4} (hb0 : b0 ≠ 1) {v w : lup10fa_Vec}
    (hv : ∀ j : Fin 4, j ≠ b0 → (lup10aj_s j).mulVec v = v)
    (hw : ∀ j : Fin 4, j ≠ b0 → (lup10aj_s j).mulVec w = w)
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
  · have h1 := lup10aj_fix_zero v (hv 1 (by decide)) (hv 2 (by decide)) (hv 3 (by decide))
    have h2 := lup10aj_fix_zero w (hw 1 (by decide)) (hw 2 (by decide)) (hw 3 (by decide))
    refine combine _ (v 0) (v 0 + v 1) (w 0) (w 0 + w 1) h1 h2 ?_
    intro hc
    apply hw0
    rw [h2, hc, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact absurd rfl hb0
  · have h1 := lup10aj_fix_two v (hv 0 (by decide)) (hv 1 (by decide)) (hv 3 (by decide))
    have h2 := lup10aj_fix_two w (hw 0 (by decide)) (hw 1 (by decide)) (hw 3 (by decide))
    refine combine _ (v 0) (v 2 + 2 * v 0) (w 0) (w 2 + 2 * w 0) h1 h2 ?_
    intro hc
    apply hw0
    rw [h2, hc, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · have h1 := lup10aj_fix_three v (hv 0 (by decide)) (hv 1 (by decide)) (hv 2 (by decide))
    have h2 := lup10aj_fix_three w (hw 0 (by decide)) (hw 1 (by decide)) (hw 2 (by decide))
    refine combine _ (v 0) (v 4 + v 0) (w 0) (w 4 + w 0) h1 h2 ?_
    intro hc
    apply hw0
    rw [h2, hc, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private theorem lup10aj_decomp (b : Fin 4) (hb : b ≠ 1)
    {m : lup10fa_Mat} (hm : m ∈ lup10aj_W)
    (hmv : m.mulVec (lup10aj_v b) = lup10aj_v b) : m ∈ lup10aj_P b := by
  have hvP : ∀ h ∈ lup10aj_P b, h.mulVec (lup10aj_v b) = lup10aj_v b := by
    intro h hh
    induction hh using Submonoid.closure_induction_left with
    | one => rw [Matrix.one_mulVec]
    | mul_left x hx y _ ih =>
        obtain ⟨j, rfl⟩ := hx
        rw [← Matrix.mulVec_mulVec, ih, lup10aj_v_fixed b hb j.1 j.2]
  have hmain : ∀ m ∈ lup10aj_W, ∃ u : Fin 8, ∃ h ∈ lup10aj_P b, m = lup10aj_rep b u * h := by
    intro m hm
    induction hm using Submonoid.closure_induction_left with
    | one => exact ⟨0, 1, Submonoid.one_mem _, by rw [lup10aj_rep_zero b hb, one_mul]⟩
    | mul_left x hx y _ ih =>
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨u, h, hhP, rfl⟩ := ih
        rcases lup10aj_step b hb i u with ⟨u', hu', -⟩ | ⟨j, hj, hrel⟩
        · exact ⟨u', h, hhP, by rw [← mul_assoc, hu']⟩
        · have hsj : lup10aj_s j ∈ lup10aj_P b :=
            Submonoid.subset_closure ⟨⟨j, hj⟩, rfl⟩
          exact ⟨u, lup10aj_s j * h, Submonoid.mul_mem (lup10aj_P b) hsj hhP,
            by rw [← mul_assoc, hrel, mul_assoc]⟩
  obtain ⟨u, h, hhP, hm_eq⟩ := hmain m hm
  have horb : (lup10aj_rep b u).mulVec (lup10aj_v b) = lup10aj_v b := by
    have h1 : m.mulVec (lup10aj_v b) =
        (lup10aj_rep b u).mulVec (h.mulVec (lup10aj_v b)) := by
      rw [hm_eq, ← Matrix.mulVec_mulVec]
    rw [hvP h hhP, hmv] at h1
    exact h1.symm
  have hu : u = 0 := lup10aj_rep_orbit_inj b hb u 0 (by
    rw [horb, lup10aj_rep_zero b hb, Matrix.one_mulVec])
  rw [hu] at hm_eq
  rw [hm_eq, lup10aj_rep_zero b hb, one_mul]
  exact hhP

private def lup10aj_Real {G : Type} [Group G] {Bs : Subgroup G} {x y : G} {L H : Subgroup G}
    (M : GGQTwoAmbModel 3 Bs x y L H) (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (ψ : MulAut ↥Bs) (m : lup10fa_Mat) : Prop :=
  ∀ v : M.V, κ (ggLin (p := 3) M.model ψ v) = m.mulVec (κ v)

private theorem lup10aj_Real_mul {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) {ψ₁ ψ₂ : MulAut ↥Bs} {m₁ m₂ : lup10fa_Mat}
    (h₁ : lup10aj_Real M κ ψ₁ m₁) (h₂ : lup10aj_Real M κ ψ₂ m₂) :
    lup10aj_Real M κ (ψ₁ * ψ₂) (m₁ * m₂) := by
  intro v
  rw [map_mul, LinearEquiv.mul_apply, h₁, h₂, Matrix.mulVec_mulVec]

private theorem lup10aj_Real_one {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) :
    lup10aj_Real M κ 1 1 := by
  intro v
  rw [map_one, Matrix.one_mulVec]
  rfl

private theorem lup10aj_Real_unique {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) {ψ₁ ψ₂ : MulAut ↥Bs} {m : lup10fa_Mat}
    (h₁ : lup10aj_Real M κ ψ₁ m) (h₂ : lup10aj_Real M κ ψ₂ m) : ψ₁ = ψ₂ := by
  refine ggLin_injective (p := 3) M.model ?_
  refine LinearEquiv.ext fun v => κ.injective ?_
  rw [h₁, h₂]

private theorem lup10aj_tau_ne_zero : ∀ j : Fin 4, lup10ab_tau j.castSucc ≠ 0 := by
  decide +kernel

private theorem lup10aj_tau_inj :
    ∀ i j : Fin 4, i ≠ j → lup10ab_tau i.castSucc ≠ lup10ab_tau j.castSucc := by
  decide +kernel

private theorem lup10aj_simple_gen {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (he0 : M.a = e 0) {k : M.ι} (hk : k ≠ M.a) :
    ∃ i : Fin 4, k = e (lup10ab_tau i.castSucc) := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin 5, e j = k := ⟨e.symm k, e.apply_symm_apply k⟩
  have hj0 : j ≠ 0 := fun h => hk (by rw [h, he0])
  fin_cases j
  · exact absurd rfl hj0
  · exact ⟨3, congrArg e (by decide)⟩
  · exact ⟨1, congrArg e (by decide)⟩
  · exact ⟨0, congrArg e (by decide)⟩
  · exact ⟨2, congrArg e (by decide)⟩

private theorem lup10aj_s_sq (i : Fin 4) : lup10aj_s i * lup10aj_s i = 1 := by
  fin_cases i <;> decide +kernel

private theorem lup10aj_s_inv (i : Fin 4) : (lup10aj_s i)⁻¹ = lup10aj_s i :=
  Matrix.inv_eq_left_inv (lup10aj_s_sq i)

private theorem lup10aj_mul_inv_apply {x y : lup10fa_Mat}
    (hx : x⁻¹ * x = 1) (hy : y⁻¹ * y = 1) : (y⁻¹ * x⁻¹) * (x * y) = 1 := by
  calc (y⁻¹ * x⁻¹) * (x * y) = y⁻¹ * (x⁻¹ * (x * y)) := by rw [mul_assoc]
    _ = y⁻¹ * ((x⁻¹ * x) * y) := by rw [mul_assoc]
    _ = y⁻¹ * (1 * y) := by rw [hx]
    _ = y⁻¹ * y := by rw [one_mul]
    _ = 1 := hy

private theorem lup10aj_mul_inv {x y : lup10fa_Mat}
    (hx : x⁻¹ * x = 1) (hy : y⁻¹ * y = 1) : (x * y)⁻¹ = y⁻¹ * x⁻¹ := by
  rw [Matrix.inv_eq_left_inv]
  exact lup10aj_mul_inv_apply hx hy

private theorem lup10aj_W_inv_mul_self :
    ∀ m ∈ lup10aj_W, m⁻¹ * m = 1 := by
  intro m hm
  induction hm using Submonoid.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [lup10aj_s_inv i]
      exact lup10aj_s_sq i
  | one => rw [inv_one, one_mul]
  | mul x y hx hy ihx ihy =>
      rw [lup10aj_mul_inv ihx ihy]
      exact lup10aj_mul_inv_apply ihx ihy

private theorem lup10aj_W_inv : ∀ m ∈ lup10aj_W, m⁻¹ ∈ lup10aj_W := by
  intro m hm
  induction hm using Submonoid.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [lup10aj_s_inv i]
      exact Submonoid.subset_closure ⟨i, rfl⟩
  | one => simp
  | mul x y hx hy ihx ihy =>
      rw [lup10aj_mul_inv (lup10aj_W_inv_mul_self x hx) (lup10aj_W_inv_mul_self y hy)]
      exact Submonoid.mul_mem lup10aj_W ihy ihx

private theorem lup10aj_Real_inv {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) {ψ : MulAut ↥Bs} {m : lup10fa_Mat}
    (h : lup10aj_Real M κ ψ m) : lup10aj_Real M κ ψ⁻¹ m⁻¹ := by
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

private theorem lup10aj_realize_W {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκs : ∀ (i : Fin 5) (v : M.V),
      κ (ggLin (p := 3) M.model (M.simple (e (lup10ab_tau i))) v) = (lup10fa_s i).mulVec (κ v))
    (he0 : M.a = e 0) :
    ∀ ψ ∈ Subgroup.closure (M.simple '' {k : M.ι | k ≠ M.a}),
      ∃ m ∈ lup10aj_W, lup10aj_Real M κ ψ m := by
  intro ψ hψ
  refine Subgroup.closure_induction
    (p := fun ψ _ => ∃ m ∈ lup10aj_W, lup10aj_Real M κ ψ m) ?_ ?_ ?_ ?_ hψ
  · rintro x ⟨k, hk, rfl⟩
    obtain ⟨i, rfl⟩ := lup10aj_simple_gen M e he0 hk
    exact ⟨lup10aj_s i, Submonoid.subset_closure ⟨i, rfl⟩, hκs i.castSucc⟩
  · exact ⟨1, Submonoid.one_mem _, lup10aj_Real_one M κ⟩
  · rintro x y _ _ ⟨mx, hmx, hrealx⟩ ⟨my, hmy, hrealy⟩
    exact ⟨mx * my, Submonoid.mul_mem lup10aj_W hmx hmy,
      lup10aj_Real_mul M κ hrealx hrealy⟩
  · rintro x _ ⟨mx, hmx, hrealx⟩
    exact ⟨mx⁻¹, lup10aj_W_inv mx hmx, lup10aj_Real_inv M κ hrealx⟩

private theorem lup10aj_yV_fixed {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκs : ∀ (i : Fin 5) (v : M.V),
      κ (ggLin (p := 3) M.model (M.simple (e (lup10ab_tau i))) v) = (lup10fa_s i).mulVec (κ v))
    (he0 : M.a = e 0) {b0 : Fin 4} (hb0 : e (lup10ab_tau b0.castSucc) = M.b) :
    ∀ j : Fin 4, j ≠ b0 → (lup10aj_s j).mulVec (κ M.yV) = κ M.yV := by
  intro j hj
  have hk1 : e (lup10ab_tau j.castSucc) ≠ M.a := by
    intro h
    exact lup10aj_tau_ne_zero j (e.injective (h.trans he0))
  have hk2 : e (lup10ab_tau j.castSucc) ≠ M.b := by
    intro h
    exact lup10aj_tau_inj j b0 hj (e.injective (h.trans hb0.symm))
  have h := hκs j.castSucc M.yV
  rw [show M.yV = M.model (Additive.ofMul ⟨y, M.hy⟩) from rfl, ggLin_apply_ofMul,
    M.y_fixed_J _ hk1 hk2] at h
  exact h.symm

private theorem lup10aj_model_pow {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (b : ↥Bs) (n : ℕ) :
    M.model (Additive.ofMul (b ^ n)) = n • M.model (Additive.ofMul b) := by
  rw [ofMul_pow, map_nsmul]

private theorem lup10aj_smul_model {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (b : ↥Bs) (t : ZMod 3) :
    t • M.model (Additive.ofMul b) = M.model (Additive.ofMul (b ^ t.val)) := by
  rw [show t • M.model (Additive.ofMul b) =
      (t.val : ZMod 3) • M.model (Additive.ofMul b) from by rw [ZMod.natCast_zmod_val],
    Nat.cast_smul_eq_nsmul, lup10aj_model_pow]

private theorem lup10aj_yV_not_mem_span {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκx : ∃ ν : ZMod 3, ν ≠ 0 ∧ κ M.xV = ν • lup10fa_x)
    (hyx : y ∉ Subgroup.zpowers x) :
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
  have hyx' : y = x ^ (t * ν⁻¹).val := by
    have h1 : M.model (Additive.ofMul ⟨y, M.hy⟩) =
        M.model (Additive.ofMul ((⟨x, M.hx⟩ : ↥Bs) ^ (t * ν⁻¹).val)) := by
      rw [show M.model (Additive.ofMul ⟨y, M.hy⟩) = M.yV from rfl, hky',
        show M.xV = M.model (Additive.ofMul ⟨x, M.hx⟩) from rfl,
        lup10aj_smul_model M ⟨x, M.hx⟩ (t * ν⁻¹)]
    have h2 : (⟨y, M.hy⟩ : ↥Bs) = ⟨x, M.hx⟩ ^ (t * ν⁻¹).val :=
      Additive.ofMul.injective (M.model.injective h1)
    exact congrArg Subtype.val h2
  exact hyx (Subgroup.mem_zpowers_iff.mpr ⟨((t * ν⁻¹).val : ℤ), by
    rw [zpow_natCast]
    exact hyx'.symm⟩)

theorem lup10d_fix_mem_parabolic {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hb2 : M.b ≠ e 2) (hbas : M.toLin.Basis) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x)
    {ψ : MulAut ↥Bs} (hψ : ψ ∈ Subgroup.closure (M.simple '' {k | k ≠ M.a}))
    (hψy : ψ ⟨y, M.hy⟩ = ⟨y, M.hy⟩) :
    ψ ∈ Subgroup.closure (M.simple '' {k | k ≠ M.a ∧ k ≠ M.b}) := by
  classical
  obtain ⟨κ, -, hκs, hκx⟩ := lup10ab_coord M e hecart he0 hbas
  obtain ⟨ν, hν0, hνx⟩ := hκx hx1
  obtain ⟨j, hj⟩ : ∃ j : Fin 5, e j = M.b := ⟨e.symm M.b, e.apply_symm_apply M.b⟩
  have hj0 : j ≠ 0 := by
    intro h
    exact M.a_ne_b (by rw [← hj, h, ← he0])
  have hj2 : j ≠ 2 := by
    intro h
    exact hb2 (by rw [← hj, h])
  have hex : ∃ b0 : Fin 4, b0 ≠ 1 ∧ e (lup10ab_tau b0.castSucc) = M.b := by
    fin_cases j
    · exact absurd rfl hj0
    · exact ⟨3, by decide, by rw [← hj]; exact congrArg e (by decide)⟩
    · exact absurd rfl hj2
    · exact ⟨0, by decide, by rw [← hj]; exact congrArg e (by decide)⟩
    · exact ⟨2, by decide, by rw [← hj]; exact congrArg e (by decide)⟩
  obtain ⟨b0, hb0ne, hb0⟩ := hex
  have hyfix : ∀ j : Fin 4, j ≠ b0 → (lup10aj_s j).mulVec (κ M.yV) = κ M.yV :=
    lup10aj_yV_fixed M e κ hκs he0 hb0
  have hvfix : ∀ j : Fin 4, j ≠ b0 → (lup10aj_s j).mulVec (lup10aj_v b0) = lup10aj_v b0 :=
    lup10aj_v_fixed b0 hb0ne
  have hvspan : lup10aj_v b0 ∉ Submodule.span (ZMod 3) {lup10fa_x} := by
    intro h
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
    exact lup10aj_v_not_span b0 hb0ne t ht
  have hyVspan : κ M.yV ∉ Submodule.span (ZMod 3) {lup10fa_x} :=
    lup10aj_yV_not_mem_span M κ ⟨ν, hν0, hνx⟩ hyx
  obtain ⟨a, c, hspan_eq⟩ := lup10aj_fix_span hb0ne hyfix hvfix hvspan
  have hc : c ≠ 0 := by
    intro hc0
    apply hyVspan
    rw [hspan_eq, hc0, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨m, hmW, hReal⟩ := lup10aj_realize_W M e κ hκs he0 ψ hψ
  have hyfixψ : ggLin (p := 3) M.model ψ M.yV = M.yV :=
    (ggLin_fix_iff (p := 3) M.model ψ ⟨y, M.hy⟩).mp hψy
  have hmfix : m.mulVec (κ M.yV) = κ M.yV := by
    rw [← hReal M.yV, hyfixψ]
  have hmx_all : ∀ m ∈ lup10aj_W, m.mulVec lup10fa_x = lup10fa_x := by
    intro m hm
    induction hm using Submonoid.closure_induction_left with
    | one => rw [Matrix.one_mulVec]
    | mul_left x hx y _ ih =>
        obtain ⟨i, rfl⟩ := hx
        rw [← Matrix.mulVec_mulVec, ih, lup10aj_s_fix_x i]
  have hmx : m.mulVec lup10fa_x = lup10fa_x := hmx_all m hmW
  have hmv : m.mulVec (lup10aj_v b0) = lup10aj_v b0 := by
    have hcalc : a • lup10fa_x + c • (m.mulVec (lup10aj_v b0)) =
        a • lup10fa_x + c • lup10aj_v b0 := by
      calc a • lup10fa_x + c • (m.mulVec (lup10aj_v b0))
          = m.mulVec (a • lup10fa_x + c • lup10aj_v b0) := by
            rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hmx]
        _ = m.mulVec (κ M.yV) := by rw [hspan_eq]
        _ = κ M.yV := hmfix
        _ = a • lup10fa_x + c • lup10aj_v b0 := hspan_eq
    have hcsmul : c • (m.mulVec (lup10aj_v b0)) = c • lup10aj_v b0 :=
      add_left_cancel hcalc
    calc m.mulVec (lup10aj_v b0)
        = c⁻¹ • (c • (m.mulVec (lup10aj_v b0))) := (inv_smul_smul₀ hc _).symm
      _ = c⁻¹ • (c • lup10aj_v b0) := by rw [hcsmul]
      _ = lup10aj_v b0 := inv_smul_smul₀ hc _
  have hmP : m ∈ lup10aj_P b0 := lup10aj_decomp b0 hb0ne hmW hmv
  have hrealP_all : ∀ m ∈ lup10aj_P b0,
      ∃ ψ' ∈ Subgroup.closure (M.simple '' {k | k ≠ M.a ∧ k ≠ M.b}),
        lup10aj_Real M κ ψ' m := by
    intro m hmP
    induction hmP using Submonoid.closure_induction_left with
    | one => exact ⟨1, Subgroup.one_mem _, lup10aj_Real_one M κ⟩
    | mul_left x hx y _ ih =>
        obtain ⟨j, rfl⟩ := hx
        obtain ⟨ψy, hψy', hrealy⟩ := ih
        have hk1 : e (lup10ab_tau j.1.castSucc) ≠ M.a := by
          intro h
          exact lup10aj_tau_ne_zero j.1 (e.injective (h.trans he0))
        have hk2 : e (lup10ab_tau j.1.castSucc) ≠ M.b := by
          intro h
          exact lup10aj_tau_inj j.1 b0 j.2 (e.injective (h.trans hb0.symm))
        refine ⟨M.simple (e (lup10ab_tau j.1.castSucc)) * ψy, ?_,
          lup10aj_Real_mul M κ (hκs j.1.castSucc) hrealy⟩
        exact mul_mem (Subgroup.subset_closure ⟨_, ⟨hk1, hk2⟩, rfl⟩) hψy'
  obtain ⟨ψ', hψ', hReal'⟩ := hrealP_all m hmP
  have hEq : ψ = ψ' := lup10aj_Real_unique M κ hReal hReal'
  rw [hEq]
  exact hψ'

theorem lup10d_labelAJ_of_fix {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (M : GGQTwoAmbModel p Bs x y L (L ⊔ K)) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hb2 : M.b ≠ e 2) (hbas : M.toLin.Basis)
    (hJaut : ∀ ψ ∈ ggAutomizer L Bs, (∀ d : ↥Bs, (d : G) ∈ D → ψ d = d) →
      ψ ∈ ggAutomizer J Bs) :
    ggAutomizer J Bs = Subgroup.closure (M.simple '' {k | k ≠ M.a ∧ k ≠ M.b}) := by
  subst hp
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hStdPre : LargeEvenStdSubPre 3 B x L D J := hcfg.2.2.1
  have hJle : J ≤ L ⊓ Subgroup.centralizer (D : Set G) := hStdPre.2.2.2.2.2.1.1
  have hJL : J ≤ L := hJle.trans inf_le_left
  have hJcent : J ≤ Subgroup.centralizer (D : Set G) := hJle.trans inf_le_right
  have hDB : D ≤ Bs := by
    rw [hStdPre.2.2.2.2.2.2]
    exact inf_le_left.trans hcfg.2.1.1
  have hD9 : Nat.card ↥D = 9 := by
    rw [hStdPre.2.2.1]
    norm_num
  have hDsup : D = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [hnb.2.1, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union]
    congr 1
  have hxp : x ^ 3 = 1 := hcfg.2.1.2.1.2 x M.hx
  have hyD : y ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (by simp)
  have hyx : y ∉ Subgroup.zpowers x := by
    intro hy
    have hDle : D ≤ Subgroup.zpowers x := by
      rw [hDsup]
      exact sup_le le_rfl (Subgroup.zpowers_le.mpr hy)
    have hle := Subgroup.card_le_of_le hDle
    rw [Nat.card_zpowers, hD9] at hle
    have hord : orderOf x ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hxp
    omega
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({(x : G)} : Set G) := hcfg.tableB_facts.2.2.2.1
  refine le_antisymm ?_ ?_
  · intro ψ hψJ
    have hψL : ψ ∈ ggAutomizer L Bs := ggAutomizer_mono Bs hJL hψJ
    have hψclosure : ψ ∈ Subgroup.closure (M.simple '' {k | k ≠ M.a}) := by
      rw [← M.automizer_L]
      exact hψL
    have hJy : J ≤ Subgroup.centralizer ({((⟨y, M.hy⟩ : ↥Bs) : G)} : Set G) := by
      refine hJcent.trans (Subgroup.centralizer_le ?_)
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hyD
    have hψy : ψ ⟨y, M.hy⟩ = ⟨y, M.hy⟩ :=
      ggAutomizer_apply_eq_of_le_centralizer hJy hψJ
    exact lup10d_fix_mem_parabolic M e hecart he0 hb2 hbas hx1 hyx hψclosure hψy
  · refine (Subgroup.closure_le _).mpr ?_
    rintro φ ⟨k, ⟨hka, hkb⟩, rfl⟩
    have hkL : M.simple k ∈ ggAutomizer L Bs := by
      rw [M.automizer_L]
      exact Subgroup.subset_closure ⟨k, hka, rfl⟩
    refine hJaut _ hkL ?_
    intro d hd
    have hrx : M.simple k ⟨x, M.hx⟩ = ⟨x, M.hx⟩ :=
      ggAutomizer_apply_eq_of_le_centralizer hLx hkL
    have hry : M.simple k ⟨y, M.hy⟩ = ⟨y, M.hy⟩ := M.y_fixed_J k hka hkb
    have hle : D.subgroupOf Bs ≤ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) ⊔
        Subgroup.zpowers (⟨y, M.hy⟩ : ↥Bs) := by
      intro b hb
      rw [Subgroup.mem_subgroupOf, hDsup] at hb
      have hmap : (Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) ⊔
          Subgroup.zpowers (⟨y, M.hy⟩ : ↥Bs)).map Bs.subtype =
          Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        rfl
      rw [← hmap] at hb
      obtain ⟨b', hb', hbb'⟩ := hb
      rwa [Subtype.ext hbb'] at hb'
    have hfix : Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) ⊔ Subgroup.zpowers (⟨y, M.hy⟩ : ↥Bs) ≤
        (M.simple k).toMonoidHom.eqLocus (MonoidHom.id ↥Bs) :=
      sup_le (Subgroup.zpowers_le.mpr hrx) (Subgroup.zpowers_le.mpr hry)
    exact hfix (hle (Subgroup.mem_subgroupOf.mpr hd))

end CFSG.StandardType

end
