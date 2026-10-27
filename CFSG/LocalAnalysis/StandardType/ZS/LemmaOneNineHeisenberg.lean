module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNinePair

public section

namespace CFSG.StandardType.ZS

section Field

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]
  {τ : K} {η₁ η₂ : U ≃ₗ[K] U} {c₁ c₂ : U} {φ₁ φ₂ : Module.Dual K U}

private theorem zs19c_mem_span_of_apply_eq_zero {v y : U}
    (ht : φ₁ c₁ ≠ 0) (hv0 : v ≠ 0) (hv : v ∈ Submodule.span K {c₁, c₂})
    (hv₁ : φ₁ v = 0) (hy : y ∈ Submodule.span K {c₁, c₂}) (hy₁ : φ₁ y = 0) :
    y ∈ Submodule.span K {v} := by
  rw [Submodule.mem_span_pair] at hv hy
  rw [Submodule.mem_span_singleton]
  obtain ⟨s, r, hv_eq⟩ := hv
  obtain ⟨α, β, hy_eq⟩ := hy
  have hr : r ≠ 0 := by
    intro hr0
    have hv0' : v = s • c₁ := by simpa [hr0] using hv_eq.symm
    have hφ : φ₁ v = s * φ₁ c₁ := by rw [hv0', map_smul, smul_eq_mul]
    have hs : s = 0 := by
      have h0 : s * φ₁ c₁ = 0 := by rw [← hφ, hv₁]
      exact (mul_eq_zero.mp h0).resolve_right ht
    rw [hs, zero_smul] at hv0'
    exact hv0 hv0'
  have har : α * r = β * s := by
    have hy₁' : φ₁ (α • c₁ + β • c₂) = 0 := by
      rw [hy_eq]
      exact hy₁
    have hv₁' : φ₁ (s • c₁ + r • c₂) = 0 := by
      rw [hv_eq]
      exact hv₁
    have h1 : α * φ₁ c₁ + β * (φ₁ c₂) = 0 := by
      simpa [map_add, map_smul, smul_eq_mul] using hy₁'
    have h2 : s * φ₁ c₁ + r * (φ₁ c₂) = 0 := by
      simpa [map_add, map_smul, smul_eq_mul] using hv₁'
    have hcomb : (α * r - β * s) * φ₁ c₁ = 0 := by
      calc
        (α * r - β * s) * φ₁ c₁ =
            r * (α * φ₁ c₁ + β * φ₁ c₂) - β * (s * φ₁ c₁ + r * φ₁ c₂) := by ring
        _ = r * 0 - β * 0 := by rw [h1, h2]
        _ = 0 := by ring
    have hzero : α * r - β * s = 0 := by
      exact (mul_eq_zero.mp hcomb).resolve_right ht
    exact sub_eq_zero.mp hzero
  have hc₁ : c₁ ≠ 0 := by
    intro hc
    rw [hc, map_zero] at ht
    exact ht rfl
  use β / r
  rw [← hy_eq, ← hv_eq]
  rw [smul_add, smul_smul, smul_smul]
  rw [div_mul_cancel₀ β hr]
  rw [add_right_cancel_iff]
  rw [smul_left_inj hc₁]
  field_simp [hr]
  rw [mul_comm r α, har]

private theorem zs19c_homology_maps_into_W {τ' : K} {g : U ≃ₗ[K] U} {c : U} {φ : Module.Dual K U}
    {W : Submodule K U} (h : IsHomologyWith τ' g c φ) (hc : c ∈ W)
    (hW : ∀ y ∈ W, φ y * φ₁ c = (τ' - 1) * φ₁ y) :
    (∀ y ∈ W, g y ∈ W ∧ φ₁ (g y) = τ' * φ₁ y) ∧ (∀ x, g x - x ∈ W) := by
  constructor
  · intro y hy
    constructor
    · rw [h.2 y]
      exact Submodule.add_mem W hy (Submodule.smul_mem W (φ y) hc)
    · rw [h.2 y, map_add, map_smul, smul_eq_mul, hW y hy]
      ring
  · intro x
    rw [h.2 x]
    simpa [add_sub_cancel_left] using Submodule.smul_mem W (φ x) hc

private theorem zs19c_double_commutator {g h : U ≃ₗ[K] U} {W : Submodule K U} {u : U}
    (hgW : ∀ x, g x - x ∈ W) (hhW : ∀ x, h x - x ∈ W)
    (hgS : ∀ y ∈ W, g y - y ∈ Submodule.span K {u})
    (hhS : ∀ y ∈ W, h y - y ∈ Submodule.span K {u}) :
    ∀ x, (g * h * g⁻¹ * h⁻¹) x - x ∈ Submodule.span K {u} := by
  intro x
  let y := g.symm (h.symm x)
  have hcomm : (g * h * g⁻¹ * h⁻¹) x = g (h y) := by simp [y, LinearEquiv.mul_apply]
  have hx : x = h (g y) := by simp [y]
  rw [hcomm, hx]
  have h1 : g (h y - y) - (h y - y) ∈ Submodule.span K {u} := hgS _ (hhW y)
  have h2 : h (g y - y) - (g y - y) ∈ Submodule.span K {u} := hhS _ (hgW y)
  have hdiff : g (h y) - h (g y) =
      (g (h y - y) - (h y - y)) - (h (g y - y) - (g y - y)) := by
    simp only [map_sub]
    abel
  rw [hdiff]
  exact Submodule.sub_mem _ h1 h2

private theorem zs19c_hW2 (h₁ : IsHomologyWith τ η₁ c₁ φ₁) (h₂ : IsHomologyWith τ η₂ c₂ φ₂)
    (hAB : (φ₁ c₂) * (φ₂ c₁) = (τ - 1) ^ 2) :
    ∀ y ∈ Submodule.span K {c₁, c₂}, φ₂ y * φ₁ c₂ = (τ - 1) * φ₁ y := by
  intro y hy
  obtain ⟨α, β, hy_eq⟩ := Submodule.mem_span_pair.mp hy
  rw [← hy_eq]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [h₁.1, h₂.1]
  linear_combination α * hAB

private theorem zs19c_exists_transvection_dependent_centres
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) (h₂ : IsHomologyWith τ η₂ c₂ φ₂)
    (hτ : τ ^ 2 ≠ 1) (hne : η₁ ≠ η₂) (hc : c₂ ∈ Submodule.span K {c₁}) :
    ∃ g ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[K] U)), QTwoLin.IsTransvectionLin g := by
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, one_pow] at hτ
    exact hτ rfl
  let H : Subgroup (U ≃ₗ[K] U) := Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[K] U))
  have hη₁ : η₁ ∈ H := Subgroup.subset_closure (by simp)
  have hη₂ : η₂ ∈ H := Subgroup.subset_closure (by simp)
  exact ⟨η₁ * η₂⁻¹, Subgroup.mul_mem H hη₁ (Subgroup.inv_mem H hη₂),
    isTransvectionLin_mul_inv_of_mem_span h₁ h₂ hτ1 hc hne⟩

private theorem zs19c_exists_transvection_ker_le
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) (h₂ : IsHomologyWith τ η₂ c₂ φ₂)
    (hτ : τ ^ 2 ≠ 1) (hne : η₁ ≠ η₂) (hk : LinearMap.ker φ₁ ≤ LinearMap.ker φ₂) :
    ∃ g ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[K] U)), QTwoLin.IsTransvectionLin g := by
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, one_pow] at hτ
    exact hτ rfl
  let H : Subgroup (U ≃ₗ[K] U) := Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[K] U))
  have hη₁ : η₁ ∈ H := Subgroup.subset_closure (by simp)
  have hη₂ : η₂ ∈ H := Subgroup.subset_closure (by simp)
  exact ⟨η₁ * η₂⁻¹, Subgroup.mul_mem H hη₁ (Subgroup.inv_mem H hη₂),
    isTransvectionLin_mul_inv_of_ker_le h₁ h₂ hτ1 hk hne⟩

private theorem zs19c_heisenberg_hAB
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) (h₂ : IsHomologyWith τ η₂ c₂ φ₂)
    (hτ1 : τ ≠ 1) {v : U} (hv0 : v ≠ 0) (hv : v ∈ Submodule.span K {c₁, c₂})
    (hv₁ : φ₁ v = 0) (hv₂ : φ₂ v = 0) :
    (τ - 1) ≠ 0 ∧ (φ₁ c₂) * (φ₂ c₁) = (τ - 1) ^ 2 ∧ (φ₁ c₂) ≠ 0 ∧ (φ₂ c₁) ≠ 0 := by
  have ht0 : τ - 1 ≠ 0 := by
    intro h
    apply hτ1
    exact sub_eq_zero.mp h
  have hAB : (φ₁ c₂) * (φ₂ c₁) = (τ - 1) ^ 2 := by
    obtain ⟨s, r, hv_eq⟩ := Submodule.mem_span_pair.mp hv
    have h1 : s * (τ - 1) + r * (φ₁ c₂) = 0 := by
      rw [← hv_eq] at hv₁
      simpa [map_add, map_smul, smul_eq_mul, h₁.1] using hv₁
    have h2 : s * (φ₂ c₁) + r * (τ - 1) = 0 := by
      rw [← hv_eq] at hv₂
      simpa [map_add, map_smul, smul_eq_mul, h₂.1] using hv₂
    by_contra hne0
    have hsub : (τ - 1) ^ 2 - (φ₁ c₂) * (φ₂ c₁) ≠ 0 := by
      intro h
      exact hne0 (sub_eq_zero.mp h).symm
    have hs : s = 0 := by
      have h : s * ((τ - 1) ^ 2 - (φ₁ c₂) * (φ₂ c₁)) = 0 := by
        linear_combination (τ - 1) * h1 - (φ₁ c₂) * h2
      exact (mul_eq_zero.mp h).resolve_right hsub
    have hr : r = 0 := by
      have h : r * ((τ - 1) ^ 2 - (φ₁ c₂) * (φ₂ c₁)) = 0 := by
        linear_combination (τ - 1) * h2 - (φ₂ c₁) * h1
      exact (mul_eq_zero.mp h).resolve_right hsub
    have hv_zero : v = 0 := by rw [← hv_eq, hs, hr, zero_smul, zero_smul, add_zero]
    exact hv0 hv_zero
  have hA : (φ₁ c₂) ≠ 0 := by
    intro h
    have h2 : (τ - 1) ^ 2 = 0 := by rw [← hAB, h, zero_mul]
    rw [pow_two] at h2
    exact ht0 (mul_self_eq_zero.mp h2)
  have hB : (φ₂ c₁) ≠ 0 := by
    intro h
    have h2 : (τ - 1) ^ 2 = 0 := by rw [← hAB, h, mul_zero]
    rw [pow_two] at h2
    exact ht0 (mul_self_eq_zero.mp h2)
  exact ⟨ht0, hAB, hA, hB⟩

private theorem zs19c_heisenberg_f
    (hk : ¬ LinearMap.ker φ₁ ≤ LinearMap.ker φ₂) :
    ∃ f' : U, φ₁ f' = 0 ∧ φ₂ f' = 1 := by
  obtain ⟨f, hf₁, hf₂⟩ := SetLike.not_le_iff_exists.mp hk
  have hf₁' : φ₁ f = 0 := by simpa using hf₁
  have hf₂' : φ₂ f ≠ 0 := by simpa using hf₂
  refine ⟨(φ₂ f)⁻¹ • f, ?_, ?_⟩
  · simp [map_smul, hf₁']
  · simp only [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hf₂'

private theorem zs19c_heisenberg_L₁
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) :
    (∀ y ∈ Submodule.span K {c₁, c₂}, η₁ y ∈ Submodule.span K {c₁, c₂} ∧
        φ₁ (η₁ y) = τ * φ₁ y) ∧
      (∀ x, η₁ x - x ∈ Submodule.span K {c₁, c₂}) := by
  have hW₁ : ∀ y ∈ Submodule.span K {c₁, c₂}, φ₁ y * φ₁ c₁ = (τ - 1) * φ₁ y := by
    intro y hy
    rw [h₁.1]
    ring
  exact zs19c_homology_maps_into_W h₁ (Submodule.subset_span (by simp)) hW₁

private theorem zs19c_heisenberg_L₂
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) (h₂ : IsHomologyWith τ η₂ c₂ φ₂)
    (hAB : (φ₁ c₂) * (φ₂ c₁) = (τ - 1) ^ 2) :
    (∀ y ∈ Submodule.span K {c₁, c₂}, η₂ y ∈ Submodule.span K {c₁, c₂} ∧
        φ₁ (η₂ y) = τ * φ₁ y) ∧
      (∀ x, η₂ x - x ∈ Submodule.span K {c₁, c₂}) := by
  have hW₂ : ∀ y ∈ Submodule.span K {c₁, c₂}, φ₂ y * φ₁ c₂ = (τ - 1) * φ₁ y :=
    zs19c_hW2 h₁ h₂ hAB
  exact zs19c_homology_maps_into_W h₂ (Submodule.subset_span (by simp)) hW₂

private theorem zs19c_heisenberg_L₁inv
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) (hτ0 : τ ≠ 0) :
    (∀ y ∈ Submodule.span K {c₁, c₂}, η₁⁻¹ y ∈ Submodule.span K {c₁, c₂} ∧
        φ₁ (η₁⁻¹ y) = τ⁻¹ * φ₁ y) ∧
      (∀ x, η₁⁻¹ x - x ∈ Submodule.span K {c₁, c₂}) := by
  have hW₁inv : ∀ y ∈ Submodule.span K {c₁, c₂},
      (-τ⁻¹ • φ₁) y * φ₁ c₁ = (τ⁻¹ - 1) * φ₁ y := by
    intro y hy
    simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [h₁.1]
    field_simp [hτ0]
    ring
  exact zs19c_homology_maps_into_W h₁.inv (Submodule.subset_span (by simp)) hW₁inv

private theorem zs19c_heisenberg_hnW
    (hL₁inv : (∀ y ∈ Submodule.span K {c₁, c₂}, η₁⁻¹ y ∈ Submodule.span K {c₁, c₂} ∧
        φ₁ (η₁⁻¹ y) = τ⁻¹ * φ₁ y) ∧
      (∀ x, η₁⁻¹ x - x ∈ Submodule.span K {c₁, c₂}))
    (hL₂ : (∀ y ∈ Submodule.span K {c₁, c₂}, η₂ y ∈ Submodule.span K {c₁, c₂} ∧
        φ₁ (η₂ y) = τ * φ₁ y) ∧
      (∀ x, η₂ x - x ∈ Submodule.span K {c₁, c₂})) :
    (∀ x, (η₂ * η₁⁻¹) x - x ∈ Submodule.span K {c₁, c₂}) ∧
      (∀ x, (η₁⁻¹ * η₂) x - x ∈ Submodule.span K {c₁, c₂}) := by
  constructor
  · intro x
    have h1 : η₂ (η₁⁻¹ x) - η₁⁻¹ x ∈ Submodule.span K {c₁, c₂} := hL₂.2 (η₁⁻¹ x)
    have h2 : η₁⁻¹ x - x ∈ Submodule.span K {c₁, c₂} := hL₁inv.2 x
    have hsum : η₂ (η₁⁻¹ x) - η₁⁻¹ x + (η₁⁻¹ x - x) ∈ Submodule.span K {c₁, c₂} :=
      Submodule.add_mem _ h1 h2
    simpa [LinearEquiv.mul_apply, sub_add_sub_cancel] using hsum
  · intro x
    have h1 : η₁⁻¹ (η₂ x) - η₂ x ∈ Submodule.span K {c₁, c₂} := hL₁inv.2 (η₂ x)
    have h2 : η₂ x - x ∈ Submodule.span K {c₁, c₂} := hL₂.2 x
    have hsum : η₁⁻¹ (η₂ x) - η₂ x + (η₂ x - x) ∈ Submodule.span K {c₁, c₂} :=
      Submodule.add_mem _ h1 h2
    simpa [LinearEquiv.mul_apply, sub_add_sub_cancel] using hsum

private theorem zs19c_heisenberg_hnS {v : U}
    (hL₁inv : (∀ y ∈ Submodule.span K {c₁, c₂}, η₁⁻¹ y ∈ Submodule.span K {c₁, c₂} ∧
        φ₁ (η₁⁻¹ y) = τ⁻¹ * φ₁ y) ∧
      (∀ x, η₁⁻¹ x - x ∈ Submodule.span K {c₁, c₂}))
    (hL₂ : (∀ y ∈ Submodule.span K {c₁, c₂}, η₂ y ∈ Submodule.span K {c₁, c₂} ∧
        φ₁ (η₂ y) = τ * φ₁ y) ∧
      (∀ x, η₂ x - x ∈ Submodule.span K {c₁, c₂}))
    (hnW : ∀ x, (η₂ * η₁⁻¹) x - x ∈ Submodule.span K {c₁, c₂})
    (hn'W : ∀ x, (η₁⁻¹ * η₂) x - x ∈ Submodule.span K {c₁, c₂})
    (hτ0 : τ ≠ 0) (hc₁ : φ₁ c₁ ≠ 0) (hv0 : v ≠ 0)
    (hv : v ∈ Submodule.span K {c₁, c₂}) (hv₁ : φ₁ v = 0) :
    (∀ y ∈ Submodule.span K {c₁, c₂},
        (η₂ * η₁⁻¹) y - y ∈ Submodule.span K {v}) ∧
      (∀ y ∈ Submodule.span K {c₁, c₂},
        (η₁⁻¹ * η₂) y - y ∈ Submodule.span K {v}) := by
  constructor
  · intro y hy
    have hyW : (η₂ * η₁⁻¹) y - y ∈ Submodule.span K {c₁, c₂} := hnW y
    have hyφ : φ₁ ((η₂ * η₁⁻¹) y - y) = 0 := by
      have h1 : φ₁ (η₂ (η₁⁻¹ y)) = τ * φ₁ (η₁⁻¹ y) :=
        (hL₂.1 (η₁⁻¹ y) (hL₁inv.1 y hy).1).2
      have h2 : φ₁ (η₁⁻¹ y) = τ⁻¹ * φ₁ y := (hL₁inv.1 y hy).2
      have h3 : φ₁ ((η₂ * η₁⁻¹) y) = φ₁ y := by
        simp only [LinearEquiv.mul_apply, h1, h2, ← mul_assoc, mul_inv_cancel₀ hτ0, one_mul]
      rw [map_sub, h3, sub_self]
    exact zs19c_mem_span_of_apply_eq_zero hc₁ hv0 hv hv₁ hyW hyφ
  · intro y hy
    have hyW : (η₁⁻¹ * η₂) y - y ∈ Submodule.span K {c₁, c₂} := hn'W y
    have hyφ : φ₁ ((η₁⁻¹ * η₂) y - y) = 0 := by
      have h1 : φ₁ (η₁⁻¹ (η₂ y)) = τ⁻¹ * φ₁ (η₂ y) :=
        (hL₁inv.1 (η₂ y) (hL₂.1 y hy).1).2
      have h2 : φ₁ (η₂ y) = τ * φ₁ y := (hL₂.1 y hy).2
      have h3 : φ₁ ((η₁⁻¹ * η₂) y) = φ₁ y := by
        simp only [LinearEquiv.mul_apply, h1, h2, ← mul_assoc, inv_mul_cancel₀ hτ0, one_mul]
      rw [map_sub, h3, sub_self]
    exact zs19c_mem_span_of_apply_eq_zero hc₁ hv0 hv hv₁ hyW hyφ

private theorem zs19c_heisenberg_v {v : U}
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) (h₂ : IsHomologyWith τ η₂ c₂ φ₂)
    (hv₁ : φ₁ v = 0) (hv₂ : φ₂ v = 0) :
    (η₂ * η₁⁻¹) v = v ∧ (η₁⁻¹ * η₂) v = v := by
  have hη₁v : η₁ v = v := h₁.apply_of_apply_eq_zero hv₁
  have hη₁inv_v : η₁⁻¹ v = v := by
    have h := congrArg (fun x => η₁⁻¹ x) hη₁v
    simpa [LinearEquiv.symm_apply_apply] using h.symm
  have hη₂v : η₂ v = v := h₂.apply_of_apply_eq_zero hv₂
  constructor
  · simp [LinearEquiv.mul_apply, hη₁inv_v, hη₂v]
  · simp [LinearEquiv.mul_apply, hη₂v, hη₁inv_v]

private theorem zs19c_heisenberg_hD
    (hτ : τ ^ 2 ≠ 1) (hτ0 : τ ≠ 0) (hA : φ₁ c₂ ≠ 0) (hB : φ₂ c₁ ≠ 0)
    (f' : U) (hf₁'' : φ₁ f' = 0) (hf₂'' : φ₂ f' = 1)
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) (h₂ : IsHomologyWith τ η₂ c₂ φ₂) :
    (τ⁻¹ + (τ⁻¹) ^ 2) * (φ₁ c₂) * (φ₂ c₁) ≠ 0 ∧
      ((η₂ * η₁⁻¹) * (η₁⁻¹ * η₂)) f' - ((η₁⁻¹ * η₂) * (η₂ * η₁⁻¹)) f' =
        ((1 - (τ⁻¹) ^ 2) * (φ₁ c₂)) • c₁ -
          ((τ⁻¹ + (τ⁻¹) ^ 2) * (φ₁ c₂) * (φ₂ c₁)) • c₂ := by
  have hsum_ne : τ⁻¹ + (τ⁻¹) ^ 2 ≠ 0 := by
    intro h
    have h1 : τ⁻¹ * (1 + τ⁻¹) = 0 := by
      rw [mul_add, mul_one, ← pow_two, h]
    have h2 : 1 + τ⁻¹ = 0 := (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hτ0)
    have h3 : τ⁻¹ = -1 := by linear_combination h2
    have h4 : τ = -1 := by
      have h' : τ * τ⁻¹ = 1 := mul_inv_cancel₀ hτ0
      rw [h3, mul_neg, mul_one] at h'
      linear_combination -h'
    have h5 : τ ^ 2 = 1 := by rw [h4]; norm_num
    exact hτ h5
  have hβ : (τ⁻¹ + (τ⁻¹) ^ 2) * (φ₁ c₂) * (φ₂ c₁) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hsum_ne hA) hB
  refine ⟨hβ, ?_⟩
  simp only [LinearEquiv.mul_apply, h₂.2, h₁.inv.2, map_add, map_smul,
    LinearMap.smul_apply, smul_eq_mul, hf₁'', hf₂'', h₁.1, h₂.1]
  match_scalars <;> field_simp [hτ0] <;> ring

private theorem zs19c_heisenberg_hw1
    (n n' : U ≃ₗ[K] U) (A B : K)
    (f' : U) (hβ : (τ⁻¹ + (τ⁻¹) ^ 2) * A * B ≠ 0)
    (hD : (n * n') f' - (n' * n) f' =
      ((1 - (τ⁻¹) ^ 2) * A) • c₁ - ((τ⁻¹ + (τ⁻¹) ^ 2) * A * B) • c₂)
    (hc : c₂ ∉ Submodule.span K {c₁}) :
    n * n' * n⁻¹ * n'⁻¹ ≠ 1 := by
  intro hw
  have hcomm : n * n' = n' * n := by
    calc n * n' = (n * n' * n⁻¹ * n'⁻¹) * (n' * n) := by group
      _ = 1 * (n' * n) := by rw [hw]
      _ = n' * n := by group
  have hcontra : (n * n') f' = (n' * n) f' := by rw [hcomm]
  have hzero : ((1 - (τ⁻¹) ^ 2) * A) • c₁ - ((τ⁻¹ + (τ⁻¹) ^ 2) * A * B) • c₂ = 0 := by
    calc ((1 - (τ⁻¹) ^ 2) * A) • c₁ - ((τ⁻¹ + (τ⁻¹) ^ 2) * A * B) • c₂ =
        (n * n') f' - (n' * n) f' := hD.symm
      _ = 0 := sub_eq_zero.mpr hcontra
  have hc₂ : c₂ ∈ Submodule.span K {c₁} := by
    have h1 : ((1 - (τ⁻¹) ^ 2) * A) • c₁ =
        ((τ⁻¹ + (τ⁻¹) ^ 2) * A * B) • c₂ := sub_eq_zero.mp hzero
    refine Submodule.mem_span_singleton.mpr
      ⟨((τ⁻¹ + (τ⁻¹) ^ 2) * A * B)⁻¹ * ((1 - (τ⁻¹) ^ 2) * A), ?_⟩
    rw [← smul_smul, h1, smul_smul, inv_mul_cancel₀ hβ, one_smul]
  exact hc hc₂

private theorem zs19c_heisenberg_w {v : U}
    (n n' : U ≃ₗ[K] U) (hn : n = η₂ * η₁⁻¹) (hn' : n' = η₁⁻¹ * η₂)
    (A B : K) (f' : U)
    (hnW : ∀ x, n x - x ∈ Submodule.span K {c₁, c₂})
    (hn'W : ∀ x, n' x - x ∈ Submodule.span K {c₁, c₂})
    (hnS : ∀ y ∈ Submodule.span K {c₁, c₂}, n y - y ∈ Submodule.span K {v})
    (hn'S : ∀ y ∈ Submodule.span K {c₁, c₂}, n' y - y ∈ Submodule.span K {v})
    (hnv : n v = v) (hn'v : n' v = v)
    (hβ : (τ⁻¹ + (τ⁻¹) ^ 2) * A * B ≠ 0)
    (hD : (n * n') f' - (n' * n) f' =
      ((1 - (τ⁻¹) ^ 2) * A) • c₁ - ((τ⁻¹ + (τ⁻¹) ^ 2) * A * B) • c₂)
    (hc : c₂ ∉ Submodule.span K {c₁}) :
    ∃ g ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[K] U)), QTwoLin.IsTransvectionLin g := by
  let w : U ≃ₗ[K] U := n * n' * n⁻¹ * n'⁻¹
  have hwH : w ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[K] U)) := by
    let H : Subgroup (U ≃ₗ[K] U) := Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[K] U))
    have hη₁ : η₁ ∈ H := Subgroup.subset_closure (by simp)
    have hη₂ : η₂ ∈ H := Subgroup.subset_closure (by simp)
    have hη₁inv : η₁⁻¹ ∈ H := Subgroup.inv_mem H hη₁
    have hnH : n ∈ H := by rw [hn]; exact Subgroup.mul_mem H hη₂ hη₁inv
    have hn'H : n' ∈ H := by rw [hn']; exact Subgroup.mul_mem H hη₁inv hη₂
    have hninvH : n⁻¹ ∈ H := Subgroup.inv_mem H hnH
    have hn'invH : n'⁻¹ ∈ H := Subgroup.inv_mem H hn'H
    exact Subgroup.mul_mem H (Subgroup.mul_mem H (Subgroup.mul_mem H hnH hn'H) hninvH) hn'invH
  have hw1 : w ≠ 1 := by
    change n * n' * n⁻¹ * n'⁻¹ ≠ 1
    exact zs19c_heisenberg_hw1 n n' A B f' hβ hD hc
  have hnv_inv : n⁻¹ v = v := by
    have h := congrArg (fun x => n⁻¹ x) hnv
    simpa [LinearEquiv.symm_apply_apply] using h.symm
  have hn'v_inv : n'⁻¹ v = v := by
    have h := congrArg (fun x => n'⁻¹ x) hn'v
    simpa [LinearEquiv.symm_apply_apply] using h.symm
  have hwv : w v = v := by
    simp only [w, LinearEquiv.mul_apply, hnv, hn'v, hnv_inv, hn'v_inv]
  have hwS : ∀ x, w x - x ∈ Submodule.span K {v} :=
    zs19c_double_commutator hnW hn'W hnS hn'S
  exact ⟨w, hwH, isTransvectionLin_of_sub_mem_span hw1 hwS hwv⟩

private theorem zs19c_exists_transvection_general
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) (h₂ : IsHomologyWith τ η₂ c₂ φ₂)
    (hτ : τ ^ 2 ≠ 1) {v : U} (hv0 : v ≠ 0)
    (hv : v ∈ Submodule.span K {c₁, c₂}) (hv₁ : φ₁ v = 0) (hv₂ : φ₂ v = 0)
    (hc : c₂ ∉ Submodule.span K {c₁}) (hk : ¬ LinearMap.ker φ₁ ≤ LinearMap.ker φ₂) :
    ∃ g ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[K] U)), QTwoLin.IsTransvectionLin g := by
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, one_pow] at hτ
    exact hτ rfl
  have hτ0 : τ ≠ 0 := h₁.type_ne_zero
  obtain ⟨ht0, hAB, hA, hB⟩ := zs19c_heisenberg_hAB h₁ h₂ hτ1 hv0 hv hv₁ hv₂
  obtain ⟨f', hf₁'', hf₂''⟩ := zs19c_heisenberg_f hk
  have hc₁ : φ₁ c₁ ≠ 0 := by rw [h₁.1]; exact ht0
  have hL₁ := zs19c_heisenberg_L₁ (c₂ := c₂) h₁
  have hL₂ := zs19c_heisenberg_L₂ h₁ h₂ hAB
  have hL₁inv := zs19c_heisenberg_L₁inv (c₂ := c₂) h₁ hτ0
  have hnW := zs19c_heisenberg_hnW hL₁inv hL₂
  have hnS := zs19c_heisenberg_hnS hL₁inv hL₂ hnW.1 hnW.2 hτ0 hc₁ hv0 hv hv₁
  have hv_prop := zs19c_heisenberg_v h₁ h₂ hv₁ hv₂
  have hD_prop := zs19c_heisenberg_hD hτ hτ0 hA hB f' hf₁'' hf₂'' h₁ h₂
  exact zs19c_heisenberg_w (η₂ * η₁⁻¹) (η₁⁻¹ * η₂) rfl rfl (φ₁ c₂) (φ₂ c₁)
    f' hnW.1 hnW.2 hnS.1 hnS.2 hv_prop.1 hv_prop.2 hD_prop.1 hD_prop.2 hc

private theorem zs19c_exists_transvection_of_mem_span_ker
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) (h₂ : IsHomologyWith τ η₂ c₂ φ₂)
    (hτ : τ ^ 2 ≠ 1) (hne : η₁ ≠ η₂) {v : U} (hv0 : v ≠ 0)
    (hv : v ∈ Submodule.span K {c₁, c₂}) (hv₁ : φ₁ v = 0) (hv₂ : φ₂ v = 0) :
    ∃ g ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[K] U)), QTwoLin.IsTransvectionLin g := by
  by_cases hc : c₂ ∈ Submodule.span K {c₁}
  · exact zs19c_exists_transvection_dependent_centres h₁ h₂ hτ hne hc
  · by_cases hk : LinearMap.ker φ₁ ≤ LinearMap.ker φ₂
    · exact zs19c_exists_transvection_ker_le h₁ h₂ hτ hne hk
    · exact zs19c_exists_transvection_general h₁ h₂ hτ hv0 hv hv₁ hv₂ hc hk

private theorem zs19c_linked_hq {H : Subgroup (U ≃ₗ[K] U)}
    (htv : QTwoLin.TransvectionFree H)
    (hη₁ : η₁ ∈ H) (hη₂ : η₂ ∈ H) (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : τ ^ 2 ≠ 1) (hτ1 : τ ≠ 1)
    (hne : η₁ ≠ η₂) (hc : c₂ ∉ Submodule.span K {c₁}) :
    φ₁ c₂ * φ₂ c₁ ≠ (τ - 1) ^ 2 := by
  intro hq
  let v : U := (φ₁ c₂) • c₁ - (τ - 1) • c₂
  have hv0 : v ≠ 0 := by
    intro hv
    apply hc
    have h2 : (τ - 1) • c₂ = (φ₁ c₂) • c₁ := (sub_eq_zero.mp hv).symm
    have hc2 : c₂ = ((τ - 1)⁻¹ * (φ₁ c₂)) • c₁ := by
      have := congrArg (fun x => (τ - 1)⁻¹ • x) h2
      simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hτ1)] using this
    exact Submodule.mem_span_singleton.mpr ⟨_, hc2.symm⟩
  have hv : v ∈ Submodule.span K {c₁, c₂} := by
    apply Submodule.sub_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hv₁ : φ₁ v = 0 := by
    simp only [v, map_sub, map_smul, smul_eq_mul, h₁.1]
    ring
  have hv₂ : φ₂ v = 0 := by
    simp only [v, map_sub, map_smul, smul_eq_mul, h₂.1]
    rw [hq]
    ring
  obtain ⟨g, hgH, hgt⟩ := zs19c_exists_transvection_of_mem_span_ker h₁ h₂ hτ hne hv0 hv hv₁ hv₂
  have hle : Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[K] U)) ≤ H :=
    (Subgroup.closure_le H).mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> assumption)
  exact htv g (hle hgH) hgt

private theorem zs19c_linked_of_not_commute {H : Subgroup (U ≃ₗ[K] U)}
    (htv : QTwoLin.TransvectionFree H)
    (hη₁ : η₁ ∈ H) (hη₂ : η₂ ∈ H) (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : τ ^ 2 ≠ 1) (hcomm : η₁ * η₂ ≠ η₂ * η₁) :
    c₂ ∉ Submodule.span K {c₁} ∧ φ₁ c₂ ≠ 0 ∧ φ₂ c₁ ≠ 0 ∧ φ₁ c₂ * φ₂ c₁ ≠ (τ - 1) ^ 2 := by
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, one_pow] at hτ
    exact hτ rfl
  have hne : η₁ ≠ η₂ := by
    intro h
    apply hcomm
    rw [h]
  have hc : c₂ ∉ Submodule.span K {c₁} := by
    intro hc
    exact htv (η₁ * η₂⁻¹) (H.mul_mem hη₁ (H.inv_mem hη₂))
      (isTransvectionLin_mul_inv_of_mem_span h₁ h₂ hτ1 hc hne)
  have hb : φ₁ c₂ ≠ 0 := by
    intro hb
    by_cases hb' : φ₂ c₁ = 0
    · exact hcomm (commute_of_apply_eq_zero h₁ h₂ hb hb')
    · exact htv (η₁ * η₂ * η₁⁻¹ * η₂⁻¹)
        (H.mul_mem (H.mul_mem (H.mul_mem hη₁ hη₂) (H.inv_mem hη₁)) (H.inv_mem hη₂))
        (isTransvectionLin_commutator_of_apply_eq_zero h₁ h₂ hτ1 hb hb')
  have hb' : φ₂ c₁ ≠ 0 := by
    intro hb'
    by_cases hb : φ₁ c₂ = 0
    · exact hcomm (commute_of_apply_eq_zero h₁ h₂ hb hb')
    · exact htv (η₂ * η₁ * η₂⁻¹ * η₁⁻¹)
        (H.mul_mem (H.mul_mem (H.mul_mem hη₂ hη₁) (H.inv_mem hη₂)) (H.inv_mem hη₁))
        (isTransvectionLin_commutator_of_apply_eq_zero h₂ h₁ hτ1 hb' hb)
  exact ⟨hc, hb, hb', zs19c_linked_hq htv hη₁ hη₂ h₁ h₂ hτ hτ1 hne hc⟩

theorem exists_transvection_of_mem_span_ker (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : τ ^ 2 ≠ 1) (hne : η₁ ≠ η₂) {v : U} (hv0 : v ≠ 0)
    (hv : v ∈ Submodule.span K {c₁, c₂}) (hv₁ : φ₁ v = 0) (hv₂ : φ₂ v = 0) :
    ∃ g ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[K] U)), QTwoLin.IsTransvectionLin g :=
  zs19c_exists_transvection_of_mem_span_ker h₁ h₂ hτ hne hv0 hv hv₁ hv₂

theorem linked_of_not_commute {H : Subgroup (U ≃ₗ[K] U)} (htv : QTwoLin.TransvectionFree H)
    (hη₁ : η₁ ∈ H) (hη₂ : η₂ ∈ H) (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : τ ^ 2 ≠ 1) (hcomm : η₁ * η₂ ≠ η₂ * η₁) :
    c₂ ∉ Submodule.span K {c₁} ∧ φ₁ c₂ ≠ 0 ∧ φ₂ c₁ ≠ 0 ∧ φ₁ c₂ * φ₂ c₁ ≠ (τ - 1) ^ 2 :=
  zs19c_linked_of_not_commute htv hη₁ hη₂ h₁ h₂ hτ hcomm

end Field

end CFSG.StandardType.ZS

end
