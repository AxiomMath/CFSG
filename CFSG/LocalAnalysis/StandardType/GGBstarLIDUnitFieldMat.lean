module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType

namespace LIDUF

open Matrix

variable {K : Type} [Field K]

@[expose] def adjM (b : K →+* K) {m n : Type*} (A : Matrix m n K) : Matrix n m K :=
  (A.map b).transpose

section Adj

variable (b : K →+* K) {m n o : Type*} [Fintype m] [Fintype n] [Fintype o]

theorem adjM_mul (A : Matrix m n K) (B : Matrix n o K) :
    adjM b (A * B) = adjM b B * adjM b A := by
  simp [adjM, Matrix.map_mul, Matrix.transpose_mul]

theorem adjM_add (A B : Matrix m n K) : adjM b (A + B) = adjM b A + adjM b B := by
  simp [adjM, Matrix.map_add, Matrix.transpose_add]

theorem adjM_one [DecidableEq m] : adjM b (1 : Matrix m m K) = 1 := by
  simp [adjM, Matrix.map_one, Matrix.transpose_one]

theorem adjM_adjM (hb : ∀ x, b (b x) = x) (A : Matrix m n K) : adjM b (adjM b A) = A := by
  ext i j
  simp [adjM, hb]

theorem adjM_map (φ : K →+* K) (hφb : ∀ x, φ (b x) = b (φ x)) (A : Matrix m n K) :
    (adjM b A).map φ = adjM b (A.map φ) := by
  ext i j
  simp [adjM, hφb]

theorem adjM_smul (c : K) (A : Matrix m n K) : adjM b (c • A) = b c • adjM b A := by
  ext i j
  simp [adjM]

end Adj

section Tv

variable (b : K →+* K) {d r : ℕ}

@[expose] def tv (U : Matrix (Fin d) (Fin r) K) : Matrix (Fin d) (Fin d) K :=
  1 + U * adjM b U

theorem adjM_tv (hb : ∀ x, b (b x) = x) (U : Matrix (Fin d) (Fin r) K) :
    adjM b (tv b U) = tv b U := by
  rw [tv, adjM_add, adjM_one, adjM_mul, adjM_adjM b hb]

theorem tv_smul_unit {c : K} (hc : c * b c = 1) (U : Matrix (Fin d) (Fin r) K) :
    tv b (c • U) = tv b U := by
  rw [tv, tv, adjM_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, one_smul]

variable [CharP K 2]

theorem tv_mul_self {U : Matrix (Fin d) (Fin r) K} (hU : adjM b U * U = 0) :
    tv b U * tv b U = 1 := by
  have h2 : ∀ M : Matrix (Fin d) (Fin d) K, M + M = 0 := fun M => by
    ext i j
    simp [Matrix.add_apply, CharTwo.add_self_eq_zero]
  have hX : (U * adjM b U) * (U * adjM b U) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (adjM b U), hU, Matrix.zero_mul, Matrix.mul_zero]
  calc tv b U * tv b U = 1 + (U * adjM b U + U * adjM b U) + (U * adjM b U) * (U * adjM b U) := by
        rw [tv]
        noncomm_ring
    _ = 1 := by rw [h2, hX]; simp

theorem det_tv {U : Matrix (Fin d) (Fin r) K} (hU : adjM b U * U = 0) : (tv b U).det = 1 := by
  rw [tv, Matrix.det_one_add_mul_comm, hU]
  simp

@[expose] def tvGL {U : Matrix (Fin d) (Fin r) K} (hU : adjM b U * U = 0) : GL (Fin d) K :=
  ⟨tv b U, tv b U, tv_mul_self b hU, tv_mul_self b hU⟩

@[simp] theorem coe_tvGL {U : Matrix (Fin d) (Fin r) K} (hU : adjM b U * U = 0) :
    ((tvGL b hU : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = tv b U := rfl

theorem tvGL_mul_self {U : Matrix (Fin d) (Fin r) K} (hU : adjM b U * U = 0) :
    tvGL b hU * tvGL b hU = 1 :=
  Units.ext (tv_mul_self b hU)

theorem tvGL_mem_unitarySU {n : ℕ} (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K)
    {U : Matrix (Fin d) (Fin r) K} (hU : adjM h.bar U * U = 0) :
    tvGL h.bar hU ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d := by
  rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h]
  refine ⟨det_tv h.bar hU, ?_⟩
  have h1 : adjM h.bar (tv h.bar U) = tv h.bar U := adjM_tv h.bar h.bar_bar U
  have h2 : (((tvGL h.bar hU : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ =
      tv h.bar U := h1
  rw [h2]
  exact tv_mul_self h.bar hU

theorem coe_inv_eq_adjM {g : GL (Fin d) K} (hg : adjM b (g : Matrix (Fin d) (Fin d) K) *
    (g : Matrix (Fin d) (Fin d) K) = 1) :
    ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = adjM b (g : Matrix (Fin d) (Fin d) K) := by
  rw [Matrix.coe_units_inv]
  exact Matrix.inv_eq_left_inv hg

theorem tv_conj (hb : ∀ x, b (b x) = x) {g : GL (Fin d) K}
    (hg : adjM b (g : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) = 1)
    (U : Matrix (Fin d) (Fin r) K) :
    (g : Matrix (Fin d) (Fin d) K) * tv b U * ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      tv b ((g : Matrix (Fin d) (Fin d) K) * U) := by
  have hinv := coe_inv_eq_adjM b hg
  have hgg : (g : Matrix (Fin d) (Fin d) K) * adjM b (g : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← hinv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hinv, tv, tv, adjM_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hgg]
  simp only [Matrix.mul_assoc]

theorem tv_mul_unitary {U : Matrix (Fin d) (Fin r) K} {P : Matrix (Fin r) (Fin r) K}
    (hP : P * adjM b P = 1) : tv b (U * P) = tv b U := by
  rw [tv, tv, adjM_mul]
  have : U * P * (adjM b P * adjM b U) = U * (P * adjM b P) * adjM b U := by
    simp only [Matrix.mul_assoc]
  rw [this, hP, Matrix.mul_one]

theorem tv_map (φ : K →+* K) (hφb : ∀ x, φ (b x) = b (φ x)) (U : Matrix (Fin d) (Fin r) K) :
    (tv b U).map φ = tv b (U.map φ) := by
  rw [tv, tv, Matrix.map_add _ (fun a₁ a₂ => map_add φ a₁ a₂), Matrix.map_mul,
    ← adjM_map b φ hφb, Matrix.map_one _ (map_zero φ) (map_one φ)]

end Tv

end LIDUF

end CFSG.StandardType

end
