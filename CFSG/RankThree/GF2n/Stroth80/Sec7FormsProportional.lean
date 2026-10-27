module

public import CFSG.RankThree.GF2n.Stroth80.Sec7OvoidEigen
public import Mathlib.LinearAlgebra.BilinearForm.Properties

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec7_forms_proportional {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (hV : Module.finrank K V = 4)
    (β₁ β₂ : LinearMap.BilinForm K V) (h₁ : β₁.Nondegenerate) (h₂ : β₂.Nondegenerate)
    (O : Set (Submodule K V)) (hO1 : ∀ P ∈ O, Module.finrank K P = 1)
    (hcard : O.ncard = Nat.card K ^ 2 + 1)
    (hline : ∀ l : Submodule K V, Module.finrank K l = 2 → {P | P ∈ O ∧ P ≤ l}.ncard ≤ 2)
    (hplane : ∀ π : Submodule K V, Module.finrank K π = 3 →
      {P | P ∈ O ∧ P ≤ π}.ncard ≤ Nat.card K + 1)
    (hperp : ∀ P ∈ O, ∀ x ∈ P, ∀ y, β₂ x y = 0 ↔ β₁ x y = 0) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ x y, β₂ x y = μ * β₁ x y := by
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨T, hTx⟩ : ∃ T : V →ₗ[K] V, ∀ x y, β₁ (T x) y = β₂ x y :=
    ⟨(β₁.toDual h₁).symm.toLinearMap.comp β₂, fun x y =>
      LinearMap.BilinForm.apply_toDual_symm_apply (hB := h₁) (β₂ x) y⟩
  have hprop : ∀ P ∈ O, ∀ x ∈ P, ∃ c : K, ∀ y, β₂ x y = c * β₁ x y := by
    intro P hP x hx
    have hk : ∀ y, β₂ x y = 0 ↔ β₁ x y = 0 := hperp P hP x hx
    by_cases h0 : ∃ y₀, β₁ x y₀ ≠ 0
    · obtain ⟨y₀, hy₀⟩ := h0
      refine ⟨β₂ x y₀ / β₁ x y₀, fun y => ?_⟩
      have hz : β₁ x (y - (β₁ x y / β₁ x y₀) • y₀) = 0 := by
        rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hy₀, sub_self]
      have hz' := (hk _).2 hz
      rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hz'
      rw [hz']
      ring
    · refine ⟨0, fun y => ?_⟩
      have hy : β₁ x y = 0 := by
        by_contra hne
        exact h0 ⟨y, hne⟩
      rw [zero_mul]
      exact (hk y).2 hy
  have hT : ∀ P ∈ O, ∀ x ∈ P, T x ∈ P := by
    intro P hP x hx
    obtain ⟨c, hc⟩ := hprop P hP x hx
    have hzero : T x - c • x = 0 := by
      refine h₁.1 (T x - c • x) fun y => ?_
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hTx x y,
        hc y, sub_self]
    rw [sub_eq_zero.1 hzero]
    exact P.smul_mem c hx
  obtain ⟨μ, hμ⟩ := sec7_ovoid_eigen_scalar hV O hO1 hcard hline hplane T hT
  have hkey : ∀ x y, β₂ x y = μ * β₁ x y := by
    intro x y
    have h := hTx x y
    rw [hμ] at h
    simpa using h.symm
  refine ⟨μ, ?_, hkey⟩
  intro hμ0
  obtain ⟨m, hm⟩ := exists_ne (0 : V)
  exact hm (h₂.1 m fun n => by rw [hkey m n, hμ0, zero_mul])

end CFSG.RankThree.GF2n.Stroth80
