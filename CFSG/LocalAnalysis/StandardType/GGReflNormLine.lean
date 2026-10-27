module

public import CFSG.LocalAnalysis.StandardType.GGReflClosedIndep

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem lna_sq {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {Λ : Type} (s : Λ → V ≃ₗ[ZMod p] V) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hs : ∀ i v, s i v = v - α i v • h i) (hα : ∀ i, α i (h i) = 2) (i : Λ) :
    s i * s i = 1 := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, hs i (s i v), hs i v, map_sub, map_smul, hα]
  change _ = v
  simp only [smul_eq_mul]
  module

theorem ggNormalizer_coroot_mem_orbit {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} (s : Λ → V ≃ₗ[ZMod p] V) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hs : ∀ i v, s i v = v - α i v • h i)
    (hα : ∀ i, α i (h i) = 2) (h0 : ∀ i, h i ≠ 0) (hRC : GGReflClosed s)
    {T : V ≃ₗ[ZMod p] V}
    (hT : T ∈ Subgroup.normalizer (Subgroup.closure (Set.range s) : Set (V ≃ₗ[ZMod p] V)))
    (j : Λ) :
    ∃ u ∈ Subgroup.closure (Set.range s), ∃ m : Λ, ∃ r : ZMod p, r ≠ 0 ∧
      T (h j) = r • u (h m) := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp
  set r0 : V ≃ₗ[ZMod p] V := T * s j * T⁻¹ with hr0
  have hr0W : r0 ∈ Subgroup.closure (Set.range s) :=
    (Subgroup.mem_normalizer_iff.mp hT (s j)).mp (Subgroup.subset_closure ⟨j, rfl⟩)
  have hr0app : ∀ w, r0 w = w - α j (T.symm w) • T (h j) := by
    intro w
    rw [hr0, LinearEquiv.mul_apply, LinearEquiv.mul_apply, show T⁻¹ = T.symm from rfl, hs,
      map_sub, map_smul, LinearEquiv.apply_symm_apply]
  have hr02 : r0 ^ 2 = 1 := by
    rw [hr0, pow_two]
    calc T * s j * T⁻¹ * (T * s j * T⁻¹) = T * (s j * s j) * T⁻¹ := by group
      _ = 1 := by rw [lna_sq s h α hs hα j]; group
  have hv0 : T (h j) ≠ 0 := fun h' => h0 j (T.injective (by rw [h', map_zero]))
  have hr0v : r0 (T (h j)) = -(T (h j)) := by
    rw [hr0app, LinearEquiv.symm_apply_apply, hα j]
    module
  have hr01 : r0 ≠ 1 := by
    intro h1
    have h3 : r0 (T (h j)) = T (h j) := by rw [h1]; rfl
    rw [hr0v] at h3
    have h2v : (2 : ZMod p) • T (h j) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h3]
      exact neg_add_cancel _
    exact hv0 ((smul_eq_zero.mp h2v).resolve_left h2)
  have hform : ∃ (v : V) (f : Module.Dual (ZMod p) V), ∀ w, r0 w = w - f w • v :=
    ⟨T (h j), (α j).comp T.symm.toLinearMap, fun w => by rw [hr0app]; rfl⟩
  obtain ⟨u, hu, m, hum⟩ := hRC r0 hr0W hr02 hr01 hform
  have hev : r0 (T (h j)) = T (h j) - α m (u.symm (T (h j))) • u (h m) := by
    rw [hum, LinearEquiv.mul_apply, LinearEquiv.mul_apply, show u⁻¹ = u.symm from rfl, hs,
      map_sub, map_smul, LinearEquiv.apply_symm_apply]
  rw [hr0v] at hev
  have hmain : T (h j) = ((2 : ZMod p)⁻¹ * α m (u.symm (T (h j)))) • u (h m) := by
    have h4 : α m (u.symm (T (h j))) • u (h m) = (2 : ZMod p) • T (h j) := by
      rw [two_smul]
      exact neg_add_eq_iff_eq_add.mp (by rw [hev]; exact sub_add_cancel _ _)
    rw [mul_smul, h4, smul_smul, inv_mul_cancel₀ h2, one_smul]
  refine ⟨u, hu, m, (2 : ZMod p)⁻¹ * α m (u.symm (T (h j))), ?_, hmain⟩
  intro hz
  rw [hz, zero_smul] at hmain
  exact hv0 hmain

theorem ggNormalizer_orbit_mem {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} (s : Λ → V ≃ₗ[ZMod p] V) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hs : ∀ i v, s i v = v - α i v • h i)
    (hα : ∀ i, α i (h i) = 2) (h0 : ∀ i, h i ≠ 0) (hRC : GGReflClosed s)
    {T : V ≃ₗ[ZMod p] V}
    (hT : T ∈ Subgroup.normalizer (Subgroup.closure (Set.range s) : Set (V ≃ₗ[ZMod p] V)))
    {u₀ : V ≃ₗ[ZMod p] V} (hu₀ : u₀ ∈ Subgroup.closure (Set.range s)) (j : Λ) :
    ∃ u ∈ Subgroup.closure (Set.range s), ∃ m : Λ, ∃ r : ZMod p, r ≠ 0 ∧
      T (u₀ (h j)) = r • u (h m) := by
  obtain ⟨u, hu, m, r, hr, hTh⟩ := ggNormalizer_coroot_mem_orbit hp s h α hs hα h0 hRC hT j
  have h1 : T * u₀ * T⁻¹ ∈ Subgroup.closure (Set.range s) :=
    (Subgroup.mem_normalizer_iff.mp hT u₀).mp hu₀
  refine ⟨(T * u₀ * T⁻¹) * u, Subgroup.mul_mem _ h1 hu, m, r, hr, ?_⟩
  have h2 : T (u₀ (h j)) = (T * u₀ * T⁻¹) (T (h j)) := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, show T⁻¹ = T.symm from rfl,
      LinearEquiv.symm_apply_apply]
  rw [h2, hTh, map_smul]
  rfl

end CFSG.StandardType
