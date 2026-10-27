module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

variable {Γ : Type*} [Group Γ]

theorem exists_mul_mem_fix (τ : Γ →* Γ) (hτ : ∀ g, τ (τ g) = g) {B T : Subgroup Γ}
    (hBT : B ⊓ B.map τ = T) (hlang : ∀ s ∈ T, τ s = s⁻¹ → ∃ r ∈ T, s = r * (τ r)⁻¹)
    {h β γ : Γ} (hβ : β ∈ B) (hγ : γ ∈ B.map τ) (hh : h⁻¹ * τ h = β * γ) :
    ∃ b ∈ B, τ (h * b) = h * b := by
  have key : ∀ x : Γ, τ (x⁻¹ * τ x) = (x⁻¹ * τ x)⁻¹ := by
    intro x
    rw [map_mul, map_inv, hτ]
    group
  obtain ⟨γ', hγ'B, hγ'eq⟩ := Subgroup.mem_map.1 hγ
  have hτγ_mem : τ γ ∈ B := by
    rw [← hγ'eq, hτ]; exact hγ'B
  set s : Γ := γ * τ β with hsdef
  have hconj : τ β * τ γ = γ⁻¹ * β⁻¹ := by
    have hz : τ (β * γ) = (β * γ)⁻¹ := by rw [← hh]; exact key h
    rwa [map_mul, mul_inv_rev] at hz
  have hs_alt : s = β⁻¹ * (τ γ)⁻¹ := by
    rw [hsdef]
    calc γ * τ β = γ * (τ β * τ γ) * (τ γ)⁻¹ := by group
      _ = γ * (γ⁻¹ * β⁻¹) * (τ γ)⁻¹ := by rw [hconj]
      _ = β⁻¹ * (τ γ)⁻¹ := by group
  have hsB : s ∈ B := by
    rw [hs_alt]
    exact B.mul_mem (B.inv_mem hβ) (B.inv_mem hτγ_mem)
  have hsmap : s ∈ B.map τ := by
    rw [hsdef]
    exact (B.map τ).mul_mem hγ (Subgroup.mem_map_of_mem τ hβ)
  have hsT : s ∈ T := by
    rw [← hBT]; exact ⟨hsB, hsmap⟩
  have hs_eq : (h * β)⁻¹ * τ (h * β) = s := by
    have e : (h * β)⁻¹ * τ (h * β) = β⁻¹ * (h⁻¹ * τ h) * τ β := by
      rw [map_mul]; group
    rw [e, hh, hsdef]; group
  have hτs : τ s = s⁻¹ := by
    rw [← hs_eq]; exact key (h * β)
  obtain ⟨r, hrT, hr_eq⟩ := hlang s hsT hτs
  have hrB : r ∈ B := (hBT ▸ inf_le_left) hrT
  refine ⟨β * r, B.mul_mem hβ hrB, ?_⟩
  have hstep : (h * (β * r))⁻¹ * τ (h * (β * r))
      = r⁻¹ * ((h * β)⁻¹ * τ (h * β)) * τ r := by
    have e2 : τ (h * (β * r)) = τ (h * β) * τ r := by
      calc τ (h * (β * r)) = τ ((h * β) * r) := by
            rw [show h * (β * r) = (h * β) * r by group]
        _ = τ (h * β) * τ r := map_mul τ (h * β) r
    have e1 : (h * (β * r))⁻¹ = r⁻¹ * (h * β)⁻¹ := by
      rw [show h * (β * r) = (h * β) * r by group]; group
    rw [e1, e2]; group
  have hone : (h * (β * r))⁻¹ * τ (h * (β * r)) = 1 := by
    rw [hstep, hs_eq, hr_eq]; group
  exact (inv_mul_eq_one.mp hone).symm

theorem exists_mul_inv_mul_eq (φ : Γ →* Γ) (hφ : ∀ g, φ (φ g) = g) {B T : Subgroup Γ} {n₀ : Γ}
    (hn₀ : φ n₀ = n₀⁻¹) (hB : ∀ b ∈ B, φ b ∈ B)
    (hBT : B ⊓ B.map (MulAut.conj n₀).toMonoidHom = T)
    (hlang : ∀ s ∈ T, n₀ * φ s * n₀⁻¹ = s⁻¹ → ∃ r ∈ T, s = r * (n₀ * φ r * n₀⁻¹)⁻¹)
    {g b₁ b₂ : Γ} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hg : g⁻¹ * φ g = b₁ * n₀ * b₂) :
    ∃ b ∈ B, (g * b)⁻¹ * φ (g * b) = n₀ := by
  set g₁ : Γ := g * b₁ with hg₁def
  set c : Γ := b₂ * φ b₁ with hcdef
  have hcB : c ∈ B := by
    rw [hcdef]; exact B.mul_mem hb₂ (hB b₁ hb₁)
  have hgg : g₁⁻¹ * φ g₁ = n₀ * c := by
    have e : g₁⁻¹ * φ g₁ = b₁⁻¹ * (g⁻¹ * φ g) * φ b₁ := by
      rw [hg₁def, map_mul]; group
    rw [e, hg, hcdef]; group
  have hφg : φ (g₁⁻¹ * φ g₁) = (g₁⁻¹ * φ g₁)⁻¹ := by
    rw [map_mul, map_inv, hφ]; group
  have h1 : φ (n₀ * c) = (n₀ * c)⁻¹ := by
    rw [← hgg]; exact hφg
  have h2 : φ n₀ * φ c = c⁻¹ * n₀⁻¹ := by
    rw [← map_mul, h1, mul_inv_rev]
  have hφc : φ c = n₀ * c⁻¹ * n₀⁻¹ := by
    rw [hn₀] at h2
    calc φ c = n₀ * (n₀⁻¹ * φ c) := by group
      _ = n₀ * (c⁻¹ * n₀⁻¹) := by rw [h2]
      _ = n₀ * c⁻¹ * n₀⁻¹ := by group
  set s : Γ := n₀ * c * n₀⁻¹ with hsdef
  have hs_eq : s = (φ c)⁻¹ := by
    rw [hsdef, hφc]; group
  have hn₀c : n₀ * c = s * n₀ := by
    rw [hsdef]; group
  have hsB : s ∈ B := by
    rw [hs_eq]; exact B.inv_mem (hB c hcB)
  have hsmap : s ∈ B.map (MulAut.conj n₀).toMonoidHom := by
    rw [hsdef]
    exact Subgroup.mem_map_of_mem (MulAut.conj n₀).toMonoidHom hcB
  have hsT : s ∈ T := by
    rw [← hBT]; exact ⟨hsB, hsmap⟩
  have hφs_c : φ s = c⁻¹ := by
    calc φ s = φ n₀ * φ c * φ (n₀⁻¹) := by
          rw [hsdef]; simp only [map_mul]
      _ = n₀⁻¹ * (n₀ * c⁻¹ * n₀⁻¹) * (n₀⁻¹)⁻¹ := by
          rw [hn₀, hφc, map_inv, hn₀]
      _ = c⁻¹ := by group
  have hφs : n₀ * φ s * n₀⁻¹ = s⁻¹ := by
    rw [hφs_c, hsdef]; group
  obtain ⟨r, hrT, hr_eq⟩ := hlang s hsT hφs
  have hrB : r ∈ B := (hBT ▸ inf_le_left) hrT
  refine ⟨b₁ * r, B.mul_mem hb₁ hrB, ?_⟩
  have hstep : (g * (b₁ * r))⁻¹ * φ (g * (b₁ * r))
      = r⁻¹ * ((g * b₁)⁻¹ * φ (g * b₁)) * φ r := by
    have e2 : φ (g * (b₁ * r)) = φ (g * b₁) * φ r := by
      calc φ (g * (b₁ * r)) = φ ((g * b₁) * r) := by
            rw [show g * (b₁ * r) = (g * b₁) * r by group]
        _ = φ (g * b₁) * φ r := map_mul φ (g * b₁) r
    have e1 : (g * (b₁ * r))⁻¹ = r⁻¹ * (g * b₁)⁻¹ := by
      rw [show g * (b₁ * r) = (g * b₁) * r by group]; group
    rw [e1, e2]; group
  have hcalc : (g * (b₁ * r))⁻¹ * φ (g * (b₁ * r)) = r⁻¹ * s * n₀ * φ r := by
    rw [hstep, hgg, hn₀c]; group
  rw [hcalc, hr_eq]; group

end CFSG.ClassicalInvolution.Phan.PhanE
