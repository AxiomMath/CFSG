module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpCases
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.QuadIsotropic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ)

variable {r : ℕ} {K : Type} [Field K]

private theorem spN_smul_right (t : K) (a c : Fin r ⊕ Fin r → K) :
    spN a (t • c) = t • spN a c := by
  ext i j
  simp only [spN, spT, vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply, Pi.smul_apply,
    Matrix.mulVec_smul, smul_eq_mul]
  ring

theorem exists_spN_inv_skew [Finite K] (hr : 2 ≤ r) (A : GL (Fin r ⊕ Fin r) K) {d : K}
    (hA : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A = (-d) • formJ r K)
    (hd : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * A = d • 1) :
    ∃ v u : Fin r ⊕ Fin r → K, v ≠ 0 ∧ u ≠ 0 ∧ spForm v u = 0 ∧
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * spN v u *
        ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          -spN v u := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hAAinv : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 := by
    simp
  have hinvA : ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 := by
    simp
  have hd0 : d ≠ 0 := by
    intro h0
    have hAA : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 0 := by rw [hd, h0, zero_smul]
    have hA0 : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 0 := by
      calc (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
          = 1 * (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := (Matrix.one_mul _).symm
        _ = (((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
              (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *
              (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by rw [hinvA]
        _ = ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
              ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
                (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [hAA, Matrix.mul_zero]
    have hone : (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 0 := by
      rw [← hAAinv, hA0, Matrix.zero_mul]
    exact one_ne_zero hone
  have hcard : 3 ≤ Fintype.card (Fin r ⊕ Fin r) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨v, hv, hquad⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.exists_isotropic_of_three_le hcard
      (formJ r K * (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
  let u : Fin r ⊕ Fin r → K :=
    (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v
  have hu_def : u = (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v := rfl
  have hvu : spForm v u = 0 := by
    rw [spForm, hu_def, Matrix.mulVec_mulVec]
    exact hquad
  have hu : u ≠ 0 := by
    intro hu0
    apply hv
    have hAv0 : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = 0 := by
      rw [← hu_def]
      exact hu0
    calc v = 1 *ᵥ v := (Matrix.one_mulVec v).symm
      _ = (((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
            (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ v := by rw [hinvA]
      _ = ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
            ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) := by
            rw [← Matrix.mulVec_mulVec]
      _ = 0 := by rw [hAv0, Matrix.mulVec_zero]
  refine ⟨v, u, hv, hu, hvu, ?_⟩
  have hAu : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ u = d • v := by
    rw [hu_def, Matrix.mulVec_mulVec, hd, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hsc : (-d)⁻¹ * d = -1 := by
    rw [inv_neg, neg_mul, inv_mul_cancel₀ hd0]
  rw [conj_spN A hA v u, ← hu_def, hAu, spN_smul_right, smul_smul, spN_comm u v, hsc,
    neg_one_smul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
