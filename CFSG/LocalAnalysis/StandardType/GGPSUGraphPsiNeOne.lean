module

public import CFSG.LocalAnalysis.StandardType.GGPSUGraphLayer0
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

private lemma psuC1_dag_B {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    psuDag h (B : Matrix (Fin n) (Fin n) K) =
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hJ : IsUnit (psuJ n K) := (AutPSU.gramJ n).isUnit
  have hG : IsUnit (psuJ n K).det :=
    (Matrix.isUnit_iff_isUnit_det (psuJ n K)).mp hJ
  exact CFSG.StandardType.ClassicalPosition.Geo.formAdj_eq_inv_of_isometry h.bar hG B
    ((mem_primeFormUnitary).mp S.B_mem)

private lemma psuC1_psi_B {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    ∃ c : Kˣ, psuPsi h X (B : Matrix (Fin n) (Fin n) K) =
      ((c⁻¹ : Kˣ) : K) • ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨c, hc⟩ := S.theta_B
  refine ⟨c, ?_⟩
  have hdag := psuC1_dag_B S
  have hNM : (B : Matrix (Fin n) (Fin n) K) *
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : psuTheta h X (B : Matrix (Fin n) (Fin n) K) *
      psuTheta h X ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← psuTheta_mul, hNM, psuTheta_one]
  rw [hc] at h1
  have h2 : psuTheta h X ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((c : K) • (B : Matrix (Fin n) (Fin n) K))⁻¹ := (Matrix.inv_eq_right_inv h1).symm
  have h3 : ((c : K) • (B : Matrix (Fin n) (Fin n) K))⁻¹ =
      ((c⁻¹ : Kˣ) : K) • ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have hprod : ((c : K) • (B : Matrix (Fin n) (Fin n) K)) *
        (((c⁻¹ : Kˣ) : K) • ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        show (c : K) * ((c⁻¹ : Kˣ) : K) = 1 by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one],
        one_smul, hNM]
    rw [Matrix.inv_eq_right_inv hprod]
  calc psuPsi h X (B : Matrix (Fin n) (Fin n) K) =
        psuTheta h X (psuDag h (B : Matrix (Fin n) (Fin n) K)) := rfl
    _ = psuTheta h X ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hdag]
    _ = ((c⁻¹ : Kˣ) : K) • ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [h2, h3]

private lemma psuC1_scalar_of_sq {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (hodd : Odd (orderOf B))
    (h : ∃ c : Kˣ, (B : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (c : K) • 1) :
    ∃ b : Kˣ, (B : Matrix (Fin n) (Fin n) K) = (b : K) • 1 := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨k, hk⟩ := hodd
  refine ⟨c ^ (k + 1), ?_⟩
  have hpow : (B : Matrix (Fin n) (Fin n) K) ^ orderOf B = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  calc (B : Matrix (Fin n) (Fin n) K)
      = (B : Matrix (Fin n) (Fin n) K) ^ (2 * k + 2) := by
        rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, pow_succ, ← hk, hpow, one_mul]
    _ = ((B : Matrix (Fin n) (Fin n) K) ^ 2) ^ (k + 1) := by
        rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]
    _ = (((c : K) • 1) : Matrix (Fin n) (Fin n) K) ^ (k + 1) := by rw [pow_two, hc]
    _ = ((c : K) ^ (k + 1)) • (1 : Matrix (Fin n) (Fin n) K) := by
        rw [← Algebra.algebraMap_eq_smul_one, ← map_pow, Algebra.algebraMap_eq_smul_one]
    _ = (((c ^ (k + 1) : Kˣ)) : K) • (1 : Matrix (Fin n) (Fin n) K) := by
        rw [Units.val_pow_eq_pow_val]

private lemma psuC1_chat_top {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
    {B : GL (Fin n) K} {b : Kˣ} (hb : (B : Matrix (Fin n) (Fin n) K) = (b : K) • 1) :
    ∀ x : AutPSU.XJ h n, x ∈ psuChat h B := by
  intro x
  refine ⟨1, ?_⟩
  rw [hb]
  simp [Matrix.mul_smul, Matrix.smul_mul]

theorem psuGraph_psi_ne_one {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    ∃ a ∈ psuAlg B, psuPsi h X a ≠ a := by
  by_contra hcon
  have hBmem : (B : Matrix (Fin n) (Fin n) K) ∈ psuAlg B :=
    Algebra.subset_adjoin ⟨B, rfl, rfl⟩
  have hBpsi : psuPsi h X (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) := by
    by_contra hne
    exact hcon ⟨B, hBmem, hne⟩
  obtain ⟨c, hc⟩ := psuC1_psi_B S
  have hBeq : (B : Matrix (Fin n) (Fin n) K) =
      ((c⁻¹ : Kˣ) : K) • ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← hBpsi, hc]
  have h1 : (B : Matrix (Fin n) (Fin n) K) *
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBsq : (B : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      ((c⁻¹ : Kˣ) : K) • 1 := by
    have hstep := congrArg (fun Y => (B : Matrix (Fin n) (Fin n) K) * Y) hBeq
    rw [hstep, Matrix.mul_smul, h1]
  obtain ⟨b, hb⟩ := psuC1_scalar_of_sq B S.odd ⟨c⁻¹, hBsq⟩
  obtain ⟨x, hx⟩ := S.not_all
  obtain ⟨d, hd⟩ := S.fix x (psuC1_chat_top hb x)
  exact hx d hd

end CFSG.StandardType
