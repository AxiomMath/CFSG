module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem bar_scalar_eq_one_or_neg_one (h : UnitaryFieldData p f K) (hr : 1 ≤ r)
    {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {c : K}
    (hc : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = c • 1) : c = 1 ∨ c = -1 := by
  have hA' : ((A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ *
      hypGram r ε K * (A : Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K :=
    mem_hypUnitary.mp hA
  let B : Matrix (HypIndex r ε) (HypIndex r ε) K :=
    ((A⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
  have hB : B * (A : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
    dsimp only [B]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAB : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * B = 1 := by
    dsimp only [B]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAmap : (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = c • B := by
    calc (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar
        = (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar := by
          rw [Matrix.one_mul]
      _ = (B * (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar := by rw [hB]
      _ = B * ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar) := by
          rw [Matrix.mul_assoc]
      _ = B * (c • 1) := by rw [hc]
      _ = c • (B * 1) := by rw [Matrix.mul_smul]
      _ = c • B := by rw [Matrix.mul_one]
  have hcJA : c • (hypGram r ε K * (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) =
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K)ᵀ * hypGram r ε K := by
    have h1 : (c • B)ᵀ * hypGram r ε K *
        (A : Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K := by
      rw [← hAmap]
      exact hA'
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul] at h1
    have hBA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K)ᵀ * Bᵀ = 1 := by
      rw [← Matrix.transpose_mul, hB, Matrix.transpose_one]
    have h4 : (A : Matrix (HypIndex r ε) (HypIndex r ε) K)ᵀ *
        (Bᵀ * hypGram r ε K * (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) =
        hypGram r ε K * (A : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
      calc (A : Matrix (HypIndex r ε) (HypIndex r ε) K)ᵀ *
            (Bᵀ * hypGram r ε K * (A : Matrix (HypIndex r ε) (HypIndex r ε) K))
          = ((A : Matrix (HypIndex r ε) (HypIndex r ε) K)ᵀ * Bᵀ) * hypGram r ε K *
              (A : Matrix (HypIndex r ε) (HypIndex r ε) K) := by noncomm_ring
        _ = hypGram r ε K * (A : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
          rw [hBA, Matrix.one_mul]
    have h5 := congrArg
      (fun M => (A : Matrix (HypIndex r ε) (HypIndex r ε) K)ᵀ * M) h1
    rw [Matrix.mul_smul, h4] at h5
    exact h5
  have hcAJ : c • ((A : Matrix (HypIndex r ε) (HypIndex r ε) K)ᵀ * hypGram r ε K) =
      hypGram r ε K * (A : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    have h5 := congrArg Matrix.transpose hcJA
    rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hypGram_transpose] at h5
    exact h5
  have h6 : (c * c) • (hypGram r ε K * (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) =
      hypGram r ε K * (A : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    rw [← smul_smul, hcJA, hcAJ]
  have hJB : (hypGram r ε K * (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) *
      (B * hypGram r ε K) = 1 := by
    rw [show hypGram r ε K * (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          (B * hypGram r ε K) =
        hypGram r ε K * ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) * B) *
          hypGram r ε K by noncomm_ring, hAB, Matrix.mul_one, hypGram_mul_self]
  have h7 : (c * c) • (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
    have h8 := congrArg (fun M => M * (B * hypGram r ε K)) h6
    rw [Matrix.smul_mul, hJB] at h8
    exact h8
  have hcc : c * c = 1 := by
    let i0 : HypIndex r ε := .inl ⟨0, hr⟩
    have h9 := congrFun (congrFun h7 i0) i0
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq] at h9
    simpa using h9
  exact mul_self_eq_one_iff.mp hcc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
