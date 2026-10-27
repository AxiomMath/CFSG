module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.Quasithin.F7Two

open Matrix Module

variable {K : Type*} [Field K] [CharP K 2]

theorem matrix_three_add_self_eq_zero (M : Matrix (Fin 3) (Fin 3) K) : M + M = 0 := by
  ext i j
  simp [CharTwo.add_self_eq_zero]

theorem exists_isUnit_mul_eq_transvection {A : Matrix (Fin 3) (Fin 3) K} (hA : A * A = 1)
    (hA1 : A ≠ 1) :
    ∃ H : Matrix (Fin 3) (Fin 3) K, IsUnit H ∧ A * H = H * Matrix.transvection 0 1 1 := by
  set N : Matrix (Fin 3) (Fin 3) K := A + 1 with hN
  have hNN : N * N = 0 := by
    have : N * N = (A * A + 1) + (A + A) := by rw [hN]; noncomm_ring
    rw [this, hA, matrix_three_add_self_eq_zero 1, matrix_three_add_self_eq_zero A, add_zero]
  have hAN : A = N + 1 := by rw [hN, add_assoc, matrix_three_add_self_eq_zero 1, add_zero]
  have hN0 : N ≠ 0 := fun h => hA1 (by rw [hAN, h, zero_add])
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → K, N *ᵥ v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hN0
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one] using this
  set b₀ : Fin 3 → K := N *ᵥ v with hb₀
  have hNb₀ : N *ᵥ b₀ = 0 := by rw [hb₀, Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  obtain ⟨b₂, hb₂, hb₂s⟩ : ∃ b₂ : Fin 3 → K, N *ᵥ b₂ = 0 ∧ b₂ ∉ Submodule.span K {b₀} := by
    by_contra hcon
    push Not at hcon
    have hle : LinearMap.ker (Matrix.toLin' N) ≤ Submodule.span K {b₀} := fun w hw =>
      hcon w (by simpa using hw)
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hv] at h1
    have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' N)
    rw [Module.finrank_fin_fun] at hrk
    have hle2 : LinearMap.range (Matrix.toLin' N) ≤ LinearMap.ker (Matrix.toLin' N) := by
      rintro _ ⟨w, rfl⟩
      simp [Matrix.mulVec_mulVec, hNN]
    have h3 := Submodule.finrank_mono hle2
    omega
  set H : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => ![b₀, v, b₂] j i with hH
  have hHx : ∀ x : Fin 3 → K, H *ᵥ x = x 0 • b₀ + x 1 • v + x 2 • b₂ := by
    intro x
    ext i
    simp [hH, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  refine ⟨H, ?_, ?_⟩
  · rw [← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have hz : H *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    suffices x - y = 0 from sub_eq_zero.mp this
    set z := x - y with hzdef
    rw [hHx] at hz
    have h1 : N *ᵥ (z 0 • b₀ + z 1 • v + z 2 • b₂) = 0 := by rw [hz, Matrix.mulVec_zero]
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hNb₀, hb₂, smul_zero, zero_add, smul_zero, add_zero] at h1
    have hz1 : z 1 = 0 := (smul_eq_zero.mp h1).resolve_right hv
    rw [hz1, zero_smul, add_zero] at hz
    have hz2 : z 2 = 0 := by
      by_contra hne
      apply hb₂s
      have : b₂ = (-(z 2)⁻¹ * z 0) • b₀ := by
        have h3 : z 2 • b₂ = -(z 0 • b₀) := eq_neg_of_add_eq_zero_right hz
        calc b₂ = (z 2)⁻¹ • (z 2 • b₂) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
          _ = (-(z 2)⁻¹ * z 0) • b₀ := by rw [h3, smul_neg, smul_smul, neg_mul, neg_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b₀)
    rw [hz2, zero_smul, add_zero] at hz
    have hz0 : z 0 = 0 := (smul_eq_zero.mp hz).resolve_right hv
    ext i
    fin_cases i
    · exact hz0
    · exact hz1
    · exact hz2
  · have hAv : ∀ w : Fin 3 → K, A *ᵥ w = N *ᵥ w + w := fun w => by
      rw [hAN, Matrix.add_mulVec, Matrix.one_mulVec]
    ext i j
    fin_cases j
    · have h0 := congrFun (hAv b₀) i
      rw [hNb₀] at h0
      simp only [Matrix.mul_apply, Fin.sum_univ_three, hH, Matrix.transvection]
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.single_apply] using h0
    · have h0 : (A *ᵥ v) i = b₀ i + v i := congrFun (hAv v) i
      simp only [Matrix.mul_apply, Fin.sum_univ_three, hH, Matrix.transvection]
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.single_apply] using h0
    · have h0 := congrFun (hAv b₂) i
      rw [hb₂] at h0
      simp only [Matrix.mul_apply, Fin.sum_univ_three, hH, Matrix.transvection]
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.single_apply] using h0

end CFSG.Quasithin.F7Two
