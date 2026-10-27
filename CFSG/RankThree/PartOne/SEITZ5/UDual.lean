module

public import CFSG.RankThree.PartOne.SEITZ5.UFrame

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem exists_dual [CharP K 2] (hσ : ∀ c, σ (σ c) = c) (P : Frame σ n) (hz0 : P.z ≠ 0) {ω : K}
    (hω : ω + σ ω = 1) :
    ∃ f : Fin n → K, herm σ f f = 0 ∧ herm σ P.z f = 1 ∧ herm σ P.e f = 0 ∧ herm σ P.u f = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨f₀, hf₀⟩ := exists_herm_eq_one σ hz0
  have hue := P.hue hσ
  have hze := P.hze hσ
  have hzu := P.hzu hσ
  set A : K := herm σ P.e f₀ with hA
  set B : K := herm σ P.u f₀ with hB
  set f₁ : Fin n → K := f₀ + A • P.u + B • P.e with hf₁
  have h1e : herm σ P.e f₁ = 0 := by
    simp only [hf₁, herm_add_right, herm_smul_right, P.he, P.heu, mul_zero, mul_one, add_zero]
    rw [← hA]
    linear_combination h2 * A
  have h1u : herm σ P.u f₁ = 0 := by
    simp only [hf₁, herm_add_right, herm_smul_right, P.hu, hue, mul_zero, mul_one, add_zero]
    rw [← hB]
    linear_combination h2 * B
  have h1z : herm σ P.z f₁ = 1 := by
    simp only [hf₁, herm_add_right, herm_smul_right, hzu, hze, mul_zero, add_zero]
    exact hf₀
  set ν : K := herm σ f₁ f₁ with hν
  have hνσ : σ ν = ν := herm_self_fixed σ hσ f₁
  set f : Fin n → K := f₁ + (ν * ω) • P.z with hf
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · have hfz : herm σ f₁ P.z = 1 := by rw [herm_conj σ hσ, h1z, map_one]
    simp only [hf, herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, P.hz, hfz,
      h1z, mul_zero, add_zero, mul_one, map_mul, hνσ]
    rw [← hν]
    linear_combination ν * hω + ν * h2
  · simp only [hf, herm_add_right, herm_smul_right, P.hz, h1z, mul_zero, add_zero]
  · simp only [hf, herm_add_right, herm_smul_right, P.hez, h1e, mul_zero, add_zero]
  · simp only [hf, herm_add_right, herm_smul_right, P.huz, h1u, mul_zero, add_zero]

theorem exists_decomp (hσ : ∀ c, σ (σ c) = c) (P : Frame σ n) {f : Fin n → K}
    (hzf : herm σ P.z f = 1) (hef : herm σ P.e f = 0) (huf : herm σ P.u f = 0)
    (v : Fin n → K) :
    ∃ (y : Fin n → K) (β α δ : K), herm σ P.e y = 0 ∧ herm σ P.u y = 0 ∧ herm σ P.z y = 0 ∧
      v = y + β • P.u + α • P.e + δ • f := by
  have hue := P.hue hσ
  have hze := P.hze hσ
  have hzu := P.hzu hσ
  refine ⟨v - herm σ P.e v • P.u - herm σ P.u v • P.e - herm σ P.z v • f, herm σ P.e v,
    herm σ P.u v, herm σ P.z v, ?_, ?_, ?_, by abel⟩
  · simp only [herm_sub_right, herm_smul_right, P.heu, P.he, hef]
    ring
  · simp only [herm_sub_right, herm_smul_right, P.hu, hue, huf]
    ring
  · simp only [herm_sub_right, herm_smul_right, hzu, hze, hzf]
    ring

theorem ext_frame (hσ : ∀ c, σ (σ c) = c) (P : Frame σ n) {f : Fin n → K}
    (hzf : herm σ P.z f = 1) (hef : herm σ P.e f = 0) (huf : herm σ P.u f = 0)
    {g g' : SUid σ n}
    (hy : ∀ y : Fin n → K, herm σ P.e y = 0 → herm σ P.u y = 0 → herm σ P.z y = 0 →
      g • y = g' • y)
    (he : g • P.e = g' • P.e) (hu : g • P.u = g' • P.u) (hf : g • f = g' • f) : g = g' := by
  apply ext_smul σ
  intro v
  obtain ⟨y, β, α, δ, h1, h2, h3, hv⟩ := exists_decomp hσ P hzf hef huf v
  rw [hv, smul_add, smul_add, smul_add, smul_add, smul_add, smul_add, smul_comm g β P.u,
    smul_comm g' β P.u, smul_comm g α P.e, smul_comm g' α P.e, smul_comm g δ f,
    smul_comm g' δ f, hy y h1 h2 h3, he, hu, hf]

end CFSG.RankThree.PartOne.SEITZ5
