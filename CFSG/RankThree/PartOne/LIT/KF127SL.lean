module

public import CFSG.RankThree.PartOne.LIT.KF127Flag
public import Mathlib.LinearAlgebra.Transvection.Basic

public section

namespace CFSG.RankThree.PartOne.LIT

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

private theorem exists_dual_of_notMem {W : Submodule (ZMod p) V} {x : V} (hx : x ∉ W) :
    ∃ ψ : Module.Dual (ZMod p) V, ψ x ≠ 0 ∧ ∀ y ∈ W, ψ y = 0 := by
  obtain ⟨ψ, hψ, hp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨ψ, hψ, fun y hy => ?_⟩
  have : ψ y ∈ W.map ψ := ⟨y, hy, rfl⟩
  rw [hp] at this
  simpa using this

theorem sl_final (hp : 3 ≤ p) (Γ Λ : Subgroup (V ≃ₗ[ZMod p] V)) (hΛΓ : Λ ≤ Γ) (v : V)
    (hv : v ≠ 0)
    (hnorm : ∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v} → ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ)
    (hfix : ∀ l ∈ Λ, l v = v) (hO : CFSG.pCore p Λ = ⊥)
    (hSL : ∀ g : V ≃ₗ[ZMod p] V, LinearMap.det (g : V →ₗ[ZMod p] V) = 1 → g ∈ Γ) :
    ∀ a ∈ Λ, ∀ b ∈ Λ, a * b = b * a := by
  set D : Submodule (ZMod p) V := Submodule.span (ZMod p) {v} with hD
  have hvD : v ∈ D := Submodule.subset_span rfl
  have hDinv : ∀ g ∈ Γ, g v ∈ D → ∀ x ∈ D, g x ∈ D := by
    intro g _ hgv x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul]
    exact D.smul_mem _ hgv
  have hmod : ∀ l ∈ Λ, ∀ y, l y - y ∈ D := by
    intro l hl y
    by_contra hy
    obtain ⟨φ, hφ, hφD⟩ := exists_dual_of_notMem hy
    have hφv : φ v = 0 := hφD v hvD
    let r : V ≃ₗ[ZMod p] V := LinearEquiv.transvection hφv
    have hrΓ : r ∈ Γ := hSL r (by
      have := LinearEquiv.transvection.det_eq_one hφv
      rw [← LinearEquiv.coe_det, this]
      simp)
    have hrf : r ∈ flagGroup D D le_rfl := by
      refine ⟨fun x => ?_, fun x _ => ?_, fun x hx => ?_⟩
      · show x + φ x • v - x ∈ D
        rw [add_sub_cancel_left]
        exact D.smul_mem _ hvD
      · show x + φ x • v - x ∈ D
        rw [add_sub_cancel_left]
        exact D.smul_mem _ hvD
      · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        show a • v + φ (a • v) • v = a • v
        rw [map_smul, hφv]
        simp
    have hcomm := flag_comm hp Γ Λ hΛΓ v hnorm hfix hO D D le_rfl hvD hDinv hDinv hrΓ hrf hl
    have h1 := congrArg (fun g => g y) hcomm
    simp only [LinearEquiv.mul_apply] at h1
    have h2 : l (r y) = l y + φ y • v := by
      show l (y + φ y • v) = _
      rw [map_add, map_smul, hfix l hl]
    have h3 : r (l y) = l y + φ (l y) • v := rfl
    rw [h2, h3] at h1
    have h4 : (φ y - φ (l y)) • v = 0 := by
      rw [sub_smul]
      have := add_left_cancel h1
      rw [this, sub_self]
    have h5 : φ y - φ (l y) = 0 := (smul_eq_zero.mp h4).resolve_right hv
    apply hφ
    rw [map_sub]
    exact sub_eq_zero.mpr (sub_eq_zero.mp h5).symm
  intro a ha b hb
  ext x
  have hbx : ∃ s : ZMod p, s • v = b x - x := Submodule.mem_span_singleton.mp (hmod b hb x)
  have hax : ∃ s : ZMod p, s • v = a x - x := Submodule.mem_span_singleton.mp (hmod a ha x)
  obtain ⟨s, hs⟩ := hbx
  obtain ⟨t, ht⟩ := hax
  have hb' : b x = x + s • v := by rw [hs]; abel
  have ha' : a x = x + t • v := by rw [ht]; abel
  show a (b x) = b (a x)
  rw [hb', ha', map_add, map_add, map_smul, map_smul, hfix a ha, hfix b hb, ha', hb']
  abel

end CFSG.RankThree.PartOne.LIT
