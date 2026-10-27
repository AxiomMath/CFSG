module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieCover
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniMat

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

private theorem ggNSLieN3A_conjTr_inv {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}
    (B : GL (Fin m) K) :
    conjTr σ ((B⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      (conjTr σ (B : Matrix (Fin m) (Fin m) K))⁻¹ := by
  have hBB : (B : Matrix (Fin m) (Fin m) K) *
      ((B⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h : conjTr σ ((B⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
      conjTr σ (B : Matrix (Fin m) (Fin m) K) = 1 := by
    rw [← conjTr_mul, hBB, conjTr_one]
  exact (Matrix.inv_eq_left_inv h).symm

private theorem ggNSLieN3A_conjTr_smul_one {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}
    (c : K) : conjTr σ (c • (1 : Matrix (Fin m) (Fin m) K)) = σ c • 1 := by
  rw [conjTr, Matrix.smul_one_eq_diagonal, Matrix.diagonal_map (map_zero σ),
    Matrix.diagonal_transpose, ← Matrix.smul_one_eq_diagonal]

private theorem ggNSLieN3A_coe_scalar {K : Type} [Field K] {m : ℕ} {c : K} (hc : c ≠ 0) :
    ((Matrix.GeneralLinearGroup.scalar (Fin m) (Units.mk0 c hc) : GL (Fin m) K) :
        Matrix (Fin m) (Fin m) K) = c • 1 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal,
    Units.val_mk0]

theorem ggNSLieN3A_gu_rescale {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)]
    [CharP K 2] {m f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) {A : GL (Fin m) K}
    (hA : A ∈ LargeEvenGUSet (Fin m) K (2 ^ f)) :
    ∃ g : GL (Fin m) K, ggIsUnitaryMat (p := 2) (f := f) g ∧
      ∀ x : GL (Fin m) K, A * (g * x * g⁻¹) * A⁻¹ = x := by
  classical
  obtain ⟨μ, hμ0, hμq, hAμ⟩ := hA
  have hμfix : unitaryInvolution K 2 f μ = μ := by
    rw [unitaryInvolution_apply]; exact hμq
  obtain ⟨c, hc⟩ := exists_norm_eq_of_fixed (p := 2) (f := f) hK hμfix hμ0
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hc
    exact hμ0 hc.symm
  let s : GL (Fin m) K := Matrix.GeneralLinearGroup.scalar (Fin m) (Units.mk0 c hc0)
  have hsdef : (s : Matrix (Fin m) (Fin m) K) = c • 1 := ggNSLieN3A_coe_scalar hc0
  refine ⟨s * A⁻¹, ?_, ?_⟩
  · have hAA : (A : Matrix (Fin m) (Fin m) K) *
        ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hAinv0 : ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
        (A : Matrix (Fin m) (Fin m) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hmap : ((A : Matrix (Fin m) (Fin m) K).map (unitaryInvolution K 2 f)) =
        (A : Matrix (Fin m) (Fin m) K).map (· ^ 2 ^ f) := by
      ext i j
      simp [iterateFrobenius_def]
    have hAμ' : conjTr (unitaryInvolution K 2 f) (A : Matrix (Fin m) (Fin m) K) *
        (A : Matrix (Fin m) (Fin m) K) = μ • 1 := by
      rw [conjTr, hmap]; exact hAμ
    have hAinv : conjTr (unitaryInvolution K 2 f) (A : Matrix (Fin m) (Fin m) K) =
        μ • ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
      calc conjTr (unitaryInvolution K 2 f) (A : Matrix (Fin m) (Fin m) K) =
            conjTr (unitaryInvolution K 2 f) (A : Matrix (Fin m) (Fin m) K) *
              ((A : Matrix (Fin m) (Fin m) K) *
                ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
              rw [hAA, Matrix.mul_one]
        _ = (conjTr (unitaryInvolution K 2 f) (A : Matrix (Fin m) (Fin m) K) *
              (A : Matrix (Fin m) (Fin m) K)) *
              ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
              rw [Matrix.mul_assoc]
        _ = (μ • (1 : Matrix (Fin m) (Fin m) K)) *
              ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by rw [hAμ']
        _ = μ • ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
              rw [Matrix.smul_mul, Matrix.one_mul]
    have hAinv' : conjTr (unitaryInvolution K 2 f)
        ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
        μ⁻¹ • (A : Matrix (Fin m) (Fin m) K) := by
      rw [ggNSLieN3A_conjTr_inv, hAinv]
      exact Matrix.inv_eq_right_inv (by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hμ0, one_smul,
          hAinv0])
    change conjTr (unitaryInvolution K 2 f)
        ((s * A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
      ((s * A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1
    rw [Units.val_mul, conjTr_mul, hsdef, ggNSLieN3A_conjTr_smul_one, hAinv']
    calc (μ⁻¹ • (A : Matrix (Fin m) (Fin m) K)) *
          (unitaryInvolution K 2 f c • (1 : Matrix (Fin m) (Fin m) K)) *
          ((c • (1 : Matrix (Fin m) (Fin m) K)) *
            ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))
        = (μ⁻¹ • (A : Matrix (Fin m) (Fin m) K)) *
            ((unitaryInvolution K 2 f c • (1 : Matrix (Fin m) (Fin m) K)) *
              (c • (1 : Matrix (Fin m) (Fin m) K))) *
            ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
          simp only [Matrix.mul_assoc]
      _ = (μ⁻¹ • (A : Matrix (Fin m) (Fin m) K)) *
            ((unitaryInvolution K 2 f c * c) • (1 : Matrix (Fin m) (Fin m) K)) *
            ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
          simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul]
      _ = (μ⁻¹ • (A : Matrix (Fin m) (Fin m) K)) *
            (μ • (1 : Matrix (Fin m) (Fin m) K)) *
            ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by rw [hc]
      _ = 1 := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_smul]
          rw [mul_inv_cancel₀ hμ0, one_smul, hAA]
  · have hscomm : ∀ y : GL (Fin m) K, y * s = s * y := by
      intro y
      have hc' : s ∈ Subgroup.center (GL (Fin m) K) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact Set.mem_range_self (Units.mk0 c hc0)
      exact Subgroup.mem_center_iff.mp hc' y
    intro x
    have hgx : (s * A⁻¹ : GL (Fin m) K) * x * (s * A⁻¹ : GL (Fin m) K)⁻¹ =
        A⁻¹ * x * A := by
      rw [_root_.mul_inv_rev, inv_inv]
      calc (s * A⁻¹) * x * (A * s⁻¹)
          = s * (A⁻¹ * x * A) * s⁻¹ := by group
        _ = (A⁻¹ * x * A) * s * s⁻¹ := by rw [← hscomm (A⁻¹ * x * A)]
        _ = A⁻¹ * x * A := by group
    rw [hgx]
    group

end CFSG.StandardType

end
