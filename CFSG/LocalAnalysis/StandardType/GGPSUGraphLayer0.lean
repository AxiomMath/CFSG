module

public import CFSG.LocalAnalysis.StandardType.GGPSUGraphDefs

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

private lemma psuLayer0a_J_mul_J (n : ℕ) (K : Type) [Field K] :
    psuJ n K * psuJ n K = (1 : Matrix (Fin n) (Fin n) K) := by
  simpa [psuJ, AutPSU.coe_gramJ] using
    (CFSG.LieType.Universal.Unitary.antidiag_mul_self (F := K) n)

private lemma psuLayer0a_J_inv (n : ℕ) (K : Type) [Field K] :
    (psuJ n K)⁻¹ = psuJ n K := by
  exact Matrix.inv_eq_right_inv (psuLayer0a_J_mul_J n K)

private lemma psuLayer0a_J_transpose (n : ℕ) (K : Type) [Field K] :
    (psuJ n K)ᵀ = psuJ n K := by
  simpa [psuJ] using (AutPSU.isPrimeFormGram_gramJ (K := K) (n := n)).symm

private lemma psuLayer0a_J_map {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) :
    (psuJ n K).map h.bar = psuJ n K := by
  simpa [psuJ] using (AutPSU.isPrimeFormGram_gramJ (K := K) (n := n)).map_eq h.bar

private lemma psuLayer0a_map_map_bar {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (a : Matrix (Fin n) (Fin n) K) : (a.map h.bar).map h.bar = a := by
  rw [Matrix.map_map]
  rw [show h.bar ∘ h.bar = id from funext h.bar_bar, Matrix.map_id]

private lemma psuLayer0a_dag_apply {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (a : Matrix (Fin n) (Fin n) K) :
    psuDag h a = psuJ n K * (a.map h.bar)ᵀ * psuJ n K := by
  simp only [psuDag, formAdj, psuLayer0a_J_inv]

private lemma psuLayer0a_conj_mul {n : ℕ} {K : Type} [Field K]
    (A B : Matrix (Fin n) (Fin n) K) :
    (psuJ n K * A * psuJ n K) * (psuJ n K * B * psuJ n K) =
      psuJ n K * (A * B) * psuJ n K := by
  calc
    (psuJ n K * A * psuJ n K) * (psuJ n K * B * psuJ n K)
        = psuJ n K * A * (psuJ n K * psuJ n K) * B * psuJ n K := by noncomm_ring
    _ = psuJ n K * A * 1 * B * psuJ n K := by rw [psuLayer0a_J_mul_J n K]
    _ = psuJ n K * (A * B) * psuJ n K := by noncomm_ring

private lemma psuLayer0a_unit_inv_mul (n : ℕ) (K : Type) [Field K] (X : GL (Fin n) K) :
    ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K) = 1 := by
  exact Units.inv_mul X

private lemma psuLayer0a_unit_mul_inv (n : ℕ) (K : Type) [Field K] (X : GL (Fin n) K) :
    (X : Matrix (Fin n) (Fin n) K) * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  exact Units.mul_inv X

private lemma psuLayer0a_unit_coe_inv (n : ℕ) (K : Type) [Field K] (X : GL (Fin n) K) :
    ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((X : Matrix (Fin n) (Fin n) K))⁻¹ := by
  exact (Matrix.inv_eq_right_inv (psuLayer0a_unit_mul_inv n K X)).symm

private lemma psuLayer0a_map_smul_bar {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (c : K) (a : Matrix (Fin n) (Fin n) K) :
    (c • a).map h.bar = h.bar c • a.map h.bar := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, map_mul]

private lemma psuLayer0a_theta_inv_eq {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K)
    (hXs : (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map h.bar = 1) :
    ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (X : Matrix (Fin n) (Fin n) K).map h.bar := by
  rw [psuLayer0a_unit_coe_inv n K X]
  exact Matrix.inv_eq_right_inv hXs

private lemma psuLayer0a_theta_inv_map {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K)
    (hXs : (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map h.bar = 1) :
    (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map h.bar =
      (X : Matrix (Fin n) (Fin n) K) := by
  rw [psuLayer0a_theta_inv_eq h X hXs]
  exact psuLayer0a_map_map_bar h (X : Matrix (Fin n) (Fin n) K)

private lemma psuLayer0a_theta_mul_aux {n : ℕ} {K : Type} [Field K]
    (X : GL (Fin n) K) (A B : Matrix (Fin n) (Fin n) K) :
    (X : Matrix (Fin n) (Fin n) K) * (A * B) *
        ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((X : Matrix (Fin n) (Fin n) K) * A *
          ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        ((X : Matrix (Fin n) (Fin n) K) * B *
          ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  symm
  calc
    ((X : Matrix (Fin n) (Fin n) K) * A *
          ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        ((X : Matrix (Fin n) (Fin n) K) * B *
          ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        = (X : Matrix (Fin n) (Fin n) K) * A *
            (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (X : Matrix (Fin n) (Fin n) K)) * B *
            ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          noncomm_ring
    _ = (X : Matrix (Fin n) (Fin n) K) * A * 1 * B *
          ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [psuLayer0a_unit_inv_mul n K X]
    _ = (X : Matrix (Fin n) (Fin n) K) * (A * B) *
          ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          noncomm_ring

private lemma psuLayer0a_theta_map_inner {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X : GL (Fin n) K)
    (hXs : (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map h.bar = 1)
    (a : Matrix (Fin n) (Fin n) K) :
    ((X : Matrix (Fin n) (Fin n) K) * a.map h.bar *
        ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map h.bar =
      (X : Matrix (Fin n) (Fin n) K).map h.bar * a * (X : Matrix (Fin n) (Fin n) K) := by
  rw [Matrix.map_mul, Matrix.map_mul, psuLayer0a_map_map_bar h a, psuLayer0a_theta_inv_map h X hXs]

theorem psuDag_add {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (a b : Matrix (Fin n) (Fin n) K) : psuDag h (a + b) = psuDag h a + psuDag h b := by
  simp [psuDag, formAdj, Matrix.map_add, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem psuDag_smul {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) (c : K)
    (a : Matrix (Fin n) (Fin n) K) : psuDag h (c • a) = h.bar c • psuDag h a := by
  simp only [psuDag, formAdj, psuLayer0a_J_inv, psuLayer0a_map_smul_bar h c a, Matrix.transpose_smul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem psuDag_mul {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (a b : Matrix (Fin n) (Fin n) K) : psuDag h (a * b) = psuDag h b * psuDag h a := by
  simp only [psuDag, formAdj, psuLayer0a_J_inv]
  rw [Matrix.map_mul, Matrix.transpose_mul]
  rw [psuLayer0a_conj_mul (A := (b.map h.bar)ᵀ) (B := (a.map h.bar)ᵀ)]

theorem psuDag_one {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) :
    psuDag h (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [psuDag, formAdj, psuLayer0a_J_inv]
  simp [Matrix.map_one, psuLayer0a_J_mul_J n K]

theorem psuDag_dag {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (a : Matrix (Fin n) (Fin n) K) : psuDag h (psuDag h a) = a := by
  rw [psuLayer0a_dag_apply h, psuLayer0a_dag_apply h]
  rw [Matrix.map_mul, Matrix.map_mul, psuLayer0a_J_map h, transpose_map,
    psuLayer0a_map_map_bar h a]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, psuLayer0a_J_transpose,
    Matrix.transpose_transpose]
  calc psuJ n K * (psuJ n K * (a * psuJ n K)) * psuJ n K
      = (psuJ n K * psuJ n K) * a * (psuJ n K * psuJ n K) := by noncomm_ring
    _ = a := by rw [psuLayer0a_J_mul_J n K]; simp

theorem psuTheta_add {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (a b : Matrix (Fin n) (Fin n) K) :
    psuTheta h X (a + b) = psuTheta h X a + psuTheta h X b := by
  simp [psuTheta, Matrix.map_add, Matrix.mul_add, Matrix.add_mul]

theorem psuTheta_smul {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (c : K) (a : Matrix (Fin n) (Fin n) K) :
    psuTheta h X (c • a) = h.bar c • psuTheta h X a := by
  simp only [psuTheta, psuLayer0a_map_smul_bar h c a, Matrix.mul_smul, Matrix.smul_mul]

theorem psuTheta_mul {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (a b : Matrix (Fin n) (Fin n) K) :
    psuTheta h X (a * b) = psuTheta h X a * psuTheta h X b := by
  simp only [psuTheta, Matrix.map_mul]
  exact psuLayer0a_theta_mul_aux X (a.map h.bar) (b.map h.bar)

theorem psuTheta_one {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) : psuTheta h X (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simp [psuTheta, Matrix.map_one, psuLayer0a_unit_mul_inv n K X]

theorem psuTheta_theta {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (hXs : (X : Matrix (Fin n) (Fin n) K) *
      (X : Matrix (Fin n) (Fin n) K).map h.bar = 1) (a : Matrix (Fin n) (Fin n) K) :
    psuTheta h X (psuTheta h X a) = a := by
  simp only [psuTheta]
  rw [psuLayer0a_theta_map_inner h X hXs a]
  calc (X : Matrix (Fin n) (Fin n) K) *
        ((X : Matrix (Fin n) (Fin n) K).map h.bar * a *
          (X : Matrix (Fin n) (Fin n) K)) *
        ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = ((X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map h.bar) *
          a * ((X : Matrix (Fin n) (Fin n) K) *
            ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by noncomm_ring
    _ = a := by rw [hXs, psuLayer0a_unit_mul_inv n K X]; simp

private theorem psuLayer0b_J_mul_self {n : ℕ} {K : Type} [Field K] :
    psuJ n K * psuJ n K = (1 : Matrix (Fin n) (Fin n) K) := by
  rw [psuJ, AutPSU.coe_gramJ, CFSG.LieType.Universal.Unitary.antidiag_mul_self]

private theorem psuLayer0b_J_inv {n : ℕ} {K : Type} [Field K] :
    (psuJ n K)⁻¹ = psuJ n K :=
  Matrix.inv_eq_right_inv (psuLayer0b_J_mul_self (n := n) (K := K))

private theorem psuLayer0b_J_transpose {n : ℕ} {K : Type} [Field K] :
    (psuJ n K)ᵀ = psuJ n K := by
  simpa only [psuJ] using (AutPSU.isPrimeFormGram_gramJ (K := K) (n := n)).symm

private theorem psuLayer0b_J_map {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) :
    (psuJ n K).map h.bar = psuJ n K := by
  simpa only [psuJ] using
    IsPrimeFormGram.map_eq (AutPSU.isPrimeFormGram_gramJ (K := K) (n := n)) h.bar

private theorem psuLayer0b_map_map {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (a : Matrix (Fin n) (Fin n) K) : (a.map h.bar).map h.bar = a := by
  ext i j
  simp only [Matrix.map_apply, h.bar_bar]

private theorem psuLayer0b_map_id {n : ℕ} {K : Type} [Field K]
    (a : Matrix (Fin n) (Fin n) K) : a.map (RingHom.id K) = a := by
  ext i j
  simp only [Matrix.map_apply, RingHom.id_apply]

private theorem psuLayer0b_map_transpose {n : ℕ} {K : Type} [Field K] (σ : K →+* K)
    (a : Matrix (Fin n) (Fin n) K) : (aᵀ).map σ = (a.map σ)ᵀ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.transpose_apply]

private theorem psuLayer0b_Xinv_eq {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K)
    (hXs : (X : Matrix (Fin n) (Fin n) K) *
      (X : Matrix (Fin n) (Fin n) K).map h.bar = 1) :
    (X : Matrix (Fin n) (Fin n) K).map h.bar =
      ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv hXs]

private theorem psuLayer0b_X_mul_Xinv {n : ℕ} {K : Type} [Field K] (X : GL (Fin n) K) :
    (X : Matrix (Fin n) (Fin n) K) *
      ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

private theorem psuLayer0b_Xinv_mul_X {n : ℕ} {K : Type} [Field K] (X : GL (Fin n) K) :
    ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (X : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

private theorem psuLayer0b_Xinv_map {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K)
    (hXs : (X : Matrix (Fin n) (Fin n) K) *
      (X : Matrix (Fin n) (Fin n) K).map h.bar = 1) :
    (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map h.bar =
      (X : Matrix (Fin n) (Fin n) K) := by
  rw [← psuLayer0b_Xinv_eq h X hXs, psuLayer0b_map_map h]

private theorem psuLayer0b_dag_eq {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (a : Matrix (Fin n) (Fin n) K) :
    psuDag h a = psuJ n K * (a.map h.bar)ᵀ * psuJ n K := by
  unfold psuDag formAdj
  rw [psuLayer0b_J_inv]

private theorem psuLayer0b_map_dag {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (a : Matrix (Fin n) (Fin n) K) :
    (psuDag h a).map h.bar = psuJ n K * aᵀ * psuJ n K := by
  rw [psuLayer0b_dag_eq h a]
  simp only [Matrix.map_mul, psuLayer0b_J_map h]
  rw [psuLayer0b_map_transpose h.bar (a.map h.bar), psuLayer0b_map_map h]

private theorem psuLayer0b_map_theta {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K)
    (hXs : (X : Matrix (Fin n) (Fin n) K) *
      (X : Matrix (Fin n) (Fin n) K).map h.bar = 1)
    (a : Matrix (Fin n) (Fin n) K) :
    (psuTheta h X a).map h.bar =
      (X : Matrix (Fin n) (Fin n) K).map h.bar * a * (X : Matrix (Fin n) (Fin n) K) := by
  simp only [psuTheta, Matrix.map_mul, psuLayer0b_map_map h, psuLayer0b_Xinv_eq h X hXs,
    psuLayer0b_Xinv_map h X hXs]

private theorem psuLayer0b_rel {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (hX : X ∈ primeFormUnitary h (psuJ n K))
    (hXs : (X : Matrix (Fin n) (Fin n) K) *
      (X : Matrix (Fin n) (Fin n) K).map h.bar = 1) :
    (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ * psuJ n K *
      (X : Matrix (Fin n) (Fin n) K) = psuJ n K := by
  simpa only [psuLayer0b_Xinv_eq h X hXs] using mem_primeFormUnitary.mp hX

private theorem psuLayer0b_J_Xinv {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (hX : X ∈ primeFormUnitary h (psuJ n K))
    (hXs : (X : Matrix (Fin n) (Fin n) K) *
      (X : Matrix (Fin n) (Fin n) K).map h.bar = 1) :
    psuJ n K * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ * psuJ n K := by
  have hrel := psuLayer0b_rel h X hX hXs
  calc psuJ n K * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ * psuJ n K *
          (X : Matrix (Fin n) (Fin n) K) *
          ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hrel]
    _ = (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ * psuJ n K := by
          rw [Matrix.mul_assoc
                ((((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ * psuJ n K)
                (X : Matrix (Fin n) (Fin n) K)
                ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
            psuLayer0b_X_mul_Xinv X, Matrix.mul_one]

private theorem psuLayer0b_X_J {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (hX : X ∈ primeFormUnitary h (psuJ n K))
    (hXs : (X : Matrix (Fin n) (Fin n) K) *
      (X : Matrix (Fin n) (Fin n) K).map h.bar = 1) :
    (X : Matrix (Fin n) (Fin n) K) * psuJ n K =
      psuJ n K * (X : Matrix (Fin n) (Fin n) K)ᵀ := by
  have hrel := psuLayer0b_rel h X hX hXs
  have htrans : (X : Matrix (Fin n) (Fin n) K)ᵀ * psuJ n K *
      ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = psuJ n K := by
    have h := congrArg Matrix.transpose hrel
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      psuLayer0b_J_transpose, ← Matrix.mul_assoc] using h
  have h1 : (X : Matrix (Fin n) (Fin n) K)ᵀ * psuJ n K =
      psuJ n K * (X : Matrix (Fin n) (Fin n) K) := by
    calc (X : Matrix (Fin n) (Fin n) K)ᵀ * psuJ n K
        = (X : Matrix (Fin n) (Fin n) K)ᵀ * psuJ n K *
            ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (X : Matrix (Fin n) (Fin n) K) := by
          rw [Matrix.mul_assoc ((X : Matrix (Fin n) (Fin n) K)ᵀ * psuJ n K)
                ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
                (X : Matrix (Fin n) (Fin n) K),
              psuLayer0b_Xinv_mul_X X, Matrix.mul_one]
      _ = psuJ n K * (X : Matrix (Fin n) (Fin n) K) := by rw [htrans]
  have hA : psuJ n K * (X : Matrix (Fin n) (Fin n) K)ᵀ * psuJ n K =
      (X : Matrix (Fin n) (Fin n) K) := by
    calc psuJ n K * (X : Matrix (Fin n) (Fin n) K)ᵀ * psuJ n K
        = psuJ n K * ((X : Matrix (Fin n) (Fin n) K)ᵀ * psuJ n K) := by
          rw [Matrix.mul_assoc (psuJ n K) (X : Matrix (Fin n) (Fin n) K)ᵀ (psuJ n K)]
      _ = psuJ n K * (psuJ n K * (X : Matrix (Fin n) (Fin n) K)) := by rw [h1]
      _ = (X : Matrix (Fin n) (Fin n) K) := by
          rw [← Matrix.mul_assoc (psuJ n K) (psuJ n K) (X : Matrix (Fin n) (Fin n) K),
            psuLayer0b_J_mul_self, Matrix.one_mul]
  calc (X : Matrix (Fin n) (Fin n) K) * psuJ n K
      = (psuJ n K * (X : Matrix (Fin n) (Fin n) K)ᵀ * psuJ n K) * psuJ n K := by
        rw [hA]
    _ = psuJ n K * (X : Matrix (Fin n) (Fin n) K)ᵀ := by
        rw [Matrix.mul_assoc (psuJ n K * (X : Matrix (Fin n) (Fin n) K)ᵀ)
              (psuJ n K) (psuJ n K),
            psuLayer0b_J_mul_self, Matrix.mul_one]

theorem psuTheta_dag {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (hX : X ∈ primeFormUnitary h (psuJ n K))
    (hXs : (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map h.bar = 1)
    (a : Matrix (Fin n) (Fin n) K) :
    psuTheta h X (psuDag h a) = psuDag h (psuTheta h X a) := by
  have hXJ := psuLayer0b_X_J h X hX hXs
  have hJX := psuLayer0b_J_Xinv h X hX hXs
  have hlhs : psuTheta h X (psuDag h a) =
      (X : Matrix (Fin n) (Fin n) K) * (psuJ n K * aᵀ * psuJ n K) *
        ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simp only [psuTheta, psuLayer0b_map_dag h a]
  have hrhs : psuDag h (psuTheta h X a) =
      psuJ n K * ((X : Matrix (Fin n) (Fin n) K)ᵀ * aᵀ *
        (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ) * psuJ n K := by
    rw [psuLayer0b_dag_eq h (psuTheta h X a), psuLayer0b_map_theta h X hXs a,
      psuLayer0b_Xinv_eq h X hXs]
    simp only [Matrix.transpose_mul]
    noncomm_ring
  rw [hlhs, hrhs]
  calc (X : Matrix (Fin n) (Fin n) K) * (psuJ n K * aᵀ * psuJ n K) *
        ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = ((X : Matrix (Fin n) (Fin n) K) * psuJ n K) * aᵀ *
          (psuJ n K * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        noncomm_ring
    _ = (psuJ n K * (X : Matrix (Fin n) (Fin n) K)ᵀ) * aᵀ *
          ((((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ * psuJ n K) := by
        rw [hXJ, hJX]
    _ = psuJ n K * ((X : Matrix (Fin n) (Fin n) K)ᵀ * aᵀ *
          ((((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ)) * psuJ n K := by
        noncomm_ring

theorem psuPsi_add {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (a b : Matrix (Fin n) (Fin n) K) :
    psuPsi h X (a + b) = psuPsi h X a + psuPsi h X b := by
  simp only [psuPsi, psuDag_add, psuTheta_add]

theorem psuPsi_smul {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (c : K) (a : Matrix (Fin n) (Fin n) K) :
    psuPsi h X (c • a) = c • psuPsi h X a := by
  simp only [psuPsi, psuDag_smul, psuTheta_smul, h.bar_bar]

theorem psuPsi_mul {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (a b : Matrix (Fin n) (Fin n) K) :
    psuPsi h X (a * b) = psuPsi h X b * psuPsi h X a := by
  simp only [psuPsi, psuDag_mul, psuTheta_mul]

theorem psuPsi_one {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) : psuPsi h X (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simp only [psuPsi, psuDag_one, psuTheta_one]

theorem psuPsi_psi {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (hX : X ∈ primeFormUnitary h (psuJ n K))
    (hXs : (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map h.bar = 1)
    (a : Matrix (Fin n) (Fin n) K) : psuPsi h X (psuPsi h X a) = a := by
  simp only [psuPsi]
  rw [← psuTheta_dag h X hX hXs (psuDag h a), psuDag_dag, psuTheta_theta h X hXs]

private theorem psuLayer0b_psi_expand {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (a : Matrix (Fin n) (Fin n) K) :
    psuPsi h X a = (X : Matrix (Fin n) (Fin n) K) *
      (psuJ n K * aᵀ * psuJ n K) * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  simp only [psuPsi, psuTheta, psuLayer0b_map_dag h a]

theorem psuPsi_eq_adjoint {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (hX : X ∈ primeFormUnitary h (psuJ n K))
    (hXs : (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map h.bar = 1)
    (a : Matrix (Fin n) (Fin n) K) :
    (psuJ n K * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ =
        psuJ n K * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      psuPsi h X a = formAdj (RingHom.id K)
        (psuJ n K * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a := by
  have hsym : (psuJ n K * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ =
      psuJ n K * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.transpose_mul, psuLayer0b_J_transpose, ← psuLayer0b_J_Xinv h X hX hXs]
  refine ⟨hsym, ?_⟩
  have hMinv : (psuJ n K * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹ =
      (X : Matrix (Fin n) (Fin n) K) * psuJ n K := by
    apply Matrix.inv_eq_right_inv
    calc (psuJ n K * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          ((X : Matrix (Fin n) (Fin n) K) * psuJ n K)
        = psuJ n K * (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (X : Matrix (Fin n) (Fin n) K)) * psuJ n K := by noncomm_ring
      _ = psuJ n K * 1 * psuJ n K := by rw [psuLayer0b_Xinv_mul_X X]
      _ = 1 := by rw [Matrix.mul_one, psuLayer0b_J_mul_self]
  rw [formAdj, psuLayer0b_map_id a, hMinv]
  rw [psuLayer0b_psi_expand h X a]
  noncomm_ring

end CFSG.StandardType
