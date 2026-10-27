module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniDefs
public import CFSG.LocalAnalysis.StandardType.GGE0PSUFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.SemisimpleCentralizers


private lemma l02qu2_scalar_mul_eq_smul {d : ℕ} {K : Type} [Field K] (c : K)
    (M : Matrix (Fin d) (Fin d) K) : Matrix.scalar (Fin d) c * M = c • M := by
  rw [show Matrix.scalar (Fin d) c = Matrix.diagonal (fun _ => c) from rfl,
    Matrix.smul_eq_diagonal_mul]

private theorem l02qu2_exists_pow_eq_inv_of_fixed {K : Type} [Field K] [Finite K] [CharP K 2]
    {q : ℕ} {μ : K} (hμ0 : μ ≠ 0) (hμq : μ ^ q = μ) :
    ∃ c : K, c ≠ 0 ∧ c ^ (q + 1) = μ⁻¹ := by
  have hsurj : Function.Surjective (fun x : K => x ^ 2) :=
    Finite.injective_iff_surjective.mp (CharTwo.sq_injective (R := K))
  obtain ⟨c, hc⟩ := hsurj μ⁻¹
  change c ^ 2 = μ⁻¹ at hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : (0 : K) = μ⁻¹ := by simpa using hc
    exact (inv_ne_zero hμ0) h0.symm
  refine ⟨c, hc0, ?_⟩
  have hsq : (c ^ q) ^ 2 = c ^ 2 := by
    calc (c ^ q) ^ 2 = c ^ (q * 2) := by rw [pow_mul]
      _ = c ^ (2 * q) := by rw [mul_comm q 2]
      _ = (c ^ 2) ^ q := by rw [pow_mul]
      _ = (μ⁻¹) ^ q := by rw [hc]
      _ = (μ ^ q)⁻¹ := by rw [inv_pow]
      _ = μ⁻¹ := by rw [hμq]
      _ = c ^ 2 := hc.symm
  have hcq : c ^ q = c := CharTwo.sq_injective hsq
  rw [pow_succ, hcq, ← sq, hc]

private lemma l02qu2_herm_scalar {d m : ℕ} {K : Type} [Field K]
    {M : Matrix (Fin d) (Fin d) K} {μ c : K}
    (hμ : Matrix.transpose (M.map (· ^ 2 ^ m)) * M = μ • (1 : Matrix (Fin d) (Fin d) K))
    (hμ0 : μ ≠ 0) (hcQ : c ^ (2 ^ m + 1) = μ⁻¹) :
    Matrix.transpose ((c • M).map (· ^ 2 ^ m)) * (c • M) = 1 := by
  have hmap : (c • M).map (· ^ 2 ^ m) = c ^ 2 ^ m • M.map (· ^ 2 ^ m) := by
    ext i j
    simp [mul_pow]
  rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hμ]
  rw [smul_smul, smul_smul, ← pow_succ, hcQ, inv_mul_cancel₀ hμ0, one_smul]

theorem exists_heldGU_scalar_mul {d m : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 2) (hm : 1 ≤ m)
    (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ 2 ^ m)
    {M : GL (Fin d) K} (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ m)) :
    ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin d) c * M ∈ Held.heldGU d K τ hτ := by
  have hF := unitaryFieldData_of_card hm hK
  haveI : CharP K 2 := hF.charP
  obtain ⟨μ, hμ0, hμq, hμ⟩ := hM
  obtain ⟨c, hc0, hcQ⟩ := l02qu2_exists_pow_eq_inv_of_fixed hμ0 hμq
  refine ⟨Units.mk0 c hc0, ?_⟩
  have hval : ((Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc0) * M : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = c • (M : Matrix (Fin d) (Fin d) K) := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    exact l02qu2_scalar_mul_eq_smul c (M : Matrix (Fin d) (Fin d) K)
  rw [Held.mem_heldGU, hval, show (⇑τ) = fun x : K => x ^ 2 ^ m from funext hτQ]
  exact l02qu2_herm_scalar hμ hμ0 hcQ

end CFSG.StandardType
