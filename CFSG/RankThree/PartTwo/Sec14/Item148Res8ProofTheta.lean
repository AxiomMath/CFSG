module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofLinRat

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix

variable {K : Type} [Field K]

theorem exists_theta {v₁ φ₁ v₂ φ₂ : Fin 3 → K} (h₁ : φ₁ ⬝ᵥ v₁ = 0) (h₂ : φ₂ ⬝ᵥ v₂ = 0)
    (hlam : φ₁ ⬝ᵥ v₂ ≠ 0) (hmu : φ₂ ⬝ᵥ v₁ ≠ 0) :
    ∃ θ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K,
      (∀ x : K, θ (uSL x) = rankOneSL v₁ φ₁ h₁ (x * (φ₁ ⬝ᵥ v₂)⁻¹)) ∧
      (∀ y : K, θ (lSL y) = rankOneSL v₂ φ₂ h₂ (y * (φ₂ ⬝ᵥ v₁)⁻¹)) := by
  set lam := φ₁ ⬝ᵥ v₂ with hlam'
  set mu := φ₂ ⬝ᵥ v₁ with hmu'
  set s := crossProduct φ₁ φ₂ with hs
  have hφ₁s : φ₁ ⬝ᵥ s = 0 := dot_self_cross φ₁ φ₂
  have hφ₂s : φ₂ ⬝ᵥ s = 0 := dot_cross_self φ₁ φ₂
  set g₀ : Matrix (Fin 3) (Fin 3) K := (Matrix.of ![v₁, v₂, s])ᵀ with hg₀
  have hdet : g₀.det ≠ 0 := by
    rw [hg₀, Matrix.det_transpose]
    have e1 : (Matrix.of ![v₁, v₂, s]).det = v₁ ⬝ᵥ crossProduct v₂ s :=
      (triple_product_eq_det v₁ v₂ s).symm
    rw [e1, triple_product_permutation, triple_product_permutation, dotProduct_comm, hs,
      cross_dot_cross, dotProduct_comm v₁ φ₁, dotProduct_comm v₂ φ₂, dotProduct_comm v₁ φ₂,
      dotProduct_comm v₂ φ₁, h₁, h₂, zero_mul, zero_sub, neg_ne_zero]
    exact mul_ne_zero hmu hlam
  set g : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero g₀ hdet with hg
  have hgM : (g : Matrix (Fin 3) (Fin 3) K) = g₀ := rfl
  have hgg : g₀ * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← hgM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcol0 : g₀.col 0 = v₁ := by
    ext r; simp [hg₀, Matrix.col_apply]
  have hcol1 : g₀.col 1 = v₂ := by
    ext r; simp [hg₀, Matrix.col_apply]
  have hrow : ∀ φ : Fin 3 → K, φ ᵥ* g₀ = ![v₁ ⬝ᵥ φ, v₂ ⬝ᵥ φ, s ⬝ᵥ φ] := by
    intro φ
    rw [hg₀, Matrix.vecMul_transpose]
    ext c
    fin_cases c <;> simp [Matrix.mulVec]
  set N := vecMulVec v₁ φ₁ with hN
  set M := vecMulVec v₂ φ₂ with hMdef
  have hI1 : N * g₀ = lam • (g₀ * single 0 1 (1 : K)) := by
    rw [hN, vecMulVec_mul, hrow, single_one_eq_vecMulVec, mul_vecMulVec, mulVec_single_one, hcol0,
      ← vecMulVec_smul]
    congr 1
    ext c
    fin_cases c
    · simp [dotProduct_comm v₁ φ₁, h₁]
    · simp [dotProduct_comm v₂ φ₁, hlam']
    · simp [dotProduct_comm s φ₁, hφ₁s]
  have hI2 : M * g₀ = mu • (g₀ * single 1 0 (1 : K)) := by
    rw [hMdef, vecMulVec_mul, hrow, single_one_eq_vecMulVec, mul_vecMulVec, mulVec_single_one,
      hcol1, ← vecMulVec_smul]
    congr 1
    ext c
    fin_cases c
    · simp [dotProduct_comm v₁ φ₂, hmu']
    · simp [dotProduct_comm v₂ φ₂, h₂]
    · simp [dotProduct_comm s φ₂, hφ₂s]
  have hconj1 : g₀ * single 0 1 (1 : K) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      lam⁻¹ • N := by
    have e : N = N * g₀ * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.mul_assoc, hgg, Matrix.mul_one]
    rw [e, hI1, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  have hconj2 : g₀ * single 1 0 (1 : K) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      mu⁻¹ • M := by
    have e : M = M * g₀ * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.mul_assoc, hgg, Matrix.mul_one]
    rw [e, hI2, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hmu, one_smul]
  have hθ_coe : ∀ A : SpecialLinearGroup (Fin 2) K,
      (((conjSL g).comp blkSL A : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        g₀ * blkMat (A : Matrix (Fin 2) (Fin 2) K) *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    fun A => coe_conjSL g (blkSL A)
  refine ⟨(conjSL g).comp blkSL, fun x => ?_, fun y => ?_⟩
  · apply Subtype.ext
    have hblk : blkMat ((uSL x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        1 + x • single 0 1 (1 : K) := by
      rw [uSL_coe]
      ext r c
      fin_cases r <;> fin_cases c <;> simp [blkMat]
    rw [hθ_coe, hblk, coe_rankOneSL, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hgg,
      Matrix.mul_smul, Matrix.smul_mul, hconj1, smul_smul]
  · apply Subtype.ext
    have hblk : blkMat ((lSL y : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        1 + y • single 1 0 (1 : K) := by
      rw [lSL_coe]
      ext r c
      fin_cases r <;> fin_cases c <;> simp [blkMat]
    rw [hθ_coe, hblk, coe_rankOneSL, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hgg,
      Matrix.mul_smul, Matrix.smul_mul, hconj2, smul_smul]

end CFSG.RankThree.PartTwo.Sec14.Item148Res8
