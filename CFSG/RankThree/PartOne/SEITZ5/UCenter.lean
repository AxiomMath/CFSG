module

public import CFSG.RankThree.PartOne.SEITZ5.UDual

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem aff_apply_f [CharP K 2] (hσ : ∀ c, σ (σ c) = c) (P : Frame σ n) {f : Fin n → K}
    (hzf : herm σ P.z f = 1) (hef : herm σ P.e f = 0)
    (huf : herm σ P.u f = 0) {g : SUid σ n} {τ₁ τ₂ : K} (h : Aff P g 1 τ₁ τ₂)
    (hT : Triv P g) : ∃ γ : K, g • f = f + σ τ₂ • P.e + σ τ₁ • P.u + γ • P.z := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hz, he, hu⟩ := h
  simp only [ent_one_zero_zero, ent_one_zero_one, ent_one_one_zero, ent_one_one_one, one_smul,
    zero_smul, add_zero, zero_add] at he hu
  have hue := P.hue hσ
  have hze := P.hze hσ
  have hzu := P.hzu hσ
  have hz1 : herm σ P.z (g • f) = 1 := by
    have := herm_smul_smul σ g P.z f
    rw [hz] at this
    rw [this, hzf]
  have he1 : herm σ P.e (g • f) = σ τ₁ := by
    have := herm_smul_smul σ g P.e f
    rw [he, hef] at this
    simp only [herm_add_left, herm_smul_left] at this
    linear_combination this - σ τ₁ * hz1 - σ τ₁ * h2
  have hu1 : herm σ P.u (g • f) = σ τ₂ := by
    have := herm_smul_smul σ g P.u f
    rw [hu, huf] at this
    simp only [herm_add_left, herm_smul_left] at this
    linear_combination this - σ τ₂ * hz1 - σ τ₂ * h2
  have hy1 : ∀ y : Fin n → K, herm σ P.e y = 0 → herm σ P.u y = 0 → herm σ P.z y = 0 →
      herm σ (g • f) y = herm σ f y := by
    intro y h1 h2' h3
    have := herm_smul_smul σ g f y
    rwa [hT y h1 h2'  h3] at this
  set w : Fin n → K := g • f - f - σ τ₂ • P.e - σ τ₁ • P.u with hw
  set μ : K := σ (herm σ w f) with hμ
  have hwy : ∀ y : Fin n → K, herm σ P.e y = 0 → herm σ P.u y = 0 → herm σ P.z y = 0 →
      herm σ (w - μ • P.z) y = 0 := by
    intro y h1 h2' h3
    simp only [hw, herm_sub_left, herm_smul_left, hy1 y h1 h2' h3, h1, h2', h3, mul_zero]
    ring
  have hwu : herm σ (w - μ • P.z) P.u = 0 := by
    have e1 : herm σ (g • f) P.u = τ₂ := by rw [herm_conj σ hσ P.u (g • f), hu1, hσ]
    have e2 : herm σ f P.u = 0 := by rw [herm_conj σ hσ P.u f, huf, map_zero]
    simp only [hw, herm_sub_left, herm_smul_left, e1, e2, P.heu, P.hu, hzu, hσ, mul_zero, mul_one]
    ring
  have hwe : herm σ (w - μ • P.z) P.e = 0 := by
    have e1 : herm σ (g • f) P.e = τ₁ := by rw [herm_conj σ hσ P.e (g • f), he1, hσ]
    have e2 : herm σ f P.e = 0 := by rw [herm_conj σ hσ P.e f, hef, map_zero]
    simp only [hw, herm_sub_left, herm_smul_left, e1, e2, P.he, hue, hze, hσ, mul_zero, mul_one]
    ring
  have hwf : herm σ (w - μ • P.z) f = 0 := by
    simp only [herm_sub_left, herm_smul_left, hzf, hμ, hσ, mul_one]
    ring
  have hzero : w - μ • P.z = 0 := by
    apply eq_zero_of_herm σ
    intro y
    obtain ⟨y₀, β, α, δ, h1, h2', h3, hv⟩ := exists_decomp hσ P hzf hef huf y
    rw [hv]
    simp only [herm_add_right, herm_smul_right, hwy y₀ h1 h2' h3, hwu, hwe, hwf, mul_zero, add_zero]
  refine ⟨μ, ?_⟩
  have : w = μ • P.z := sub_eq_zero.1 hzero
  rw [hw] at this
  linear_combination this

theorem mul_comm_aff [CharP K 2] (hσ : ∀ c, σ (σ c) = c) (P : Frame σ n) {f : Fin n → K}
    (hzf : herm σ P.z f = 1) (hef : herm σ P.e f = 0) (huf : herm σ P.u f = 0)
    {g₁ g₂ : SUid σ n} {τ : K} (h₁ : Aff P g₁ 1 τ 0) (h₂ : Aff P g₂ 1 0 1) (T₁ : Triv P g₁)
    (T₂ : Triv P g₂) :
    IsTv σ (g₁ * g₂ * (g₂ * g₁)⁻¹) P.z (τ + σ τ) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hzu := P.hzu hσ
  have hze := P.hze hσ
  obtain ⟨γ₁, hγ₁⟩ := aff_apply_f hσ P hzf hef huf h₁ T₁
  obtain ⟨γ₂, hγ₂⟩ := aff_apply_f hσ P hzf hef huf h₂ T₂
  obtain ⟨hz₁, he₁, hu₁⟩ := h₁
  obtain ⟨hz₂, he₂, hu₂⟩ := h₂
  simp only [ent_one_zero_zero, ent_one_zero_one, ent_one_one_zero, ent_one_one_one, one_smul,
    zero_smul, add_zero, zero_add] at he₁ hu₁ he₂ hu₂
  simp only [map_zero, map_one, one_smul, zero_smul, add_zero] at hγ₁ hγ₂
  have hc : (τ + σ τ) + σ (τ + σ τ) = 0 := by
    rw [map_add, hσ]
    linear_combination (τ + σ τ) * h2
  set X : SUid σ n := tv hσ P.hz hc with hX
  have hXs : ∀ v, X • v = v + ((τ + σ τ) * herm σ P.z v) • P.z := tv_smul hσ P.hz hc
  have key : g₁ * g₂ = X * (g₂ * g₁) := by
    refine ext_frame hσ P hzf hef huf ?_ ?_ ?_ ?_
    · intro y h1 h2' h3
      simp only [mul_smul, T₁ y h1 h2' h3, T₂ y h1 h2' h3, hXs, h3, mul_zero, zero_smul, add_zero]
    · simp only [mul_smul, he₂, he₁, smul_add, smul_comm g₂ τ P.z, hz₂, hXs, herm_add_right,
        herm_smul_right, hze, P.hz, mul_zero, add_zero, zero_smul]
    · simp only [mul_smul, hu₂, hu₁, smul_add, hz₁, hXs, herm_add_right, hzu, P.hz, mul_zero,
        add_zero, zero_smul]
    · simp only [mul_smul, hγ₂, hγ₁, smul_add, smul_comm g₁ γ₂ P.z, smul_comm g₂ (σ τ) P.u,
        smul_comm g₂ γ₁ P.z, he₁, hz₁, hz₂, hu₂, hXs, herm_add_right, herm_smul_right, hzf,
        hze, hzu, P.hz, mul_zero, add_zero, mul_one]
      match_scalars <;> first | ring1 | linear_combination (-(σ τ)) * h2
  have hXeq : g₁ * g₂ * (g₂ * g₁)⁻¹ = X := by
    rw [mul_inv_eq_iff_eq_mul]
    exact key
  rw [hXeq]
  exact hXs

end CFSG.RankThree.PartOne.SEITZ5
