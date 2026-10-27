module

public import CFSG.LocalAnalysis.StandardType.GGF4N2ChartQuad
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.ClassicalInvolution.WeakCT.Defs
public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.StandardType.N2Chart

open Matrix Polynomial CFSG.ClassicalInvolution.Phan

variable {n : ℕ}

@[expose] noncomputable def quadMat (c : F4) (X : Matrix (Fin n) (Fin n) F4) : Matrix (Fin n) (Fin n) F4 :=
  (X * X + c • X + 1) * (X - 1)

theorem quadMat_mulVec (c : F4) (X : Matrix (Fin n) (Fin n) F4) (w : Fin n → F4) :
    quadMat c X *ᵥ w = X *ᵥ (X *ᵥ (X *ᵥ w - w)) + c • (X *ᵥ (X *ᵥ w - w)) + (X *ᵥ w - w) := by
  rw [quadMat, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.add_mulVec,
    Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem quadOm_kills_iff (s : SL6) (c : F4) :
    (∀ v ∈ suppSp s, aeval (endo s) (quadOm c) v = 0) ↔
      quadMat c (s : Matrix (Fin 6) (Fin 6) F4) = 0 := by
  have hsupp : ∀ w : V6,
      ((Matrix.toLin' (s : Matrix (Fin 6) (Fin 6) F4) - LinearMap.id : V6 →ₗ[F4] V6) w) =
        (s : Matrix (Fin 6) (Fin 6) F4) *ᵥ w - w := fun w => by
    rw [LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply]
  have hq : ∀ v : V6, aeval (endo s) (quadOm c) v =
      (s : Matrix (Fin 6) (Fin 6) F4) *ᵥ ((s : Matrix (Fin 6) (Fin 6) F4) *ᵥ v) +
        c • ((s : Matrix (Fin 6) (Fin 6) F4) *ᵥ v) + v := fun v => by
    rw [aeval_quadOm_apply, endo_apply, endo_apply]
  constructor
  · intro h
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, quadMat_mulVec, ← hq]
    exact h _ ⟨w, hsupp w⟩
  · rintro h v ⟨w, rfl⟩
    rw [hsupp, hq, ← quadMat_mulVec, h, Matrix.zero_mulVec]

theorem quadMat_conj (c : F4) {A B : Matrix (Fin n) (Fin n) F4} (hAB : A * B = 1)
    (hBA : B * A = 1) (X : Matrix (Fin n) (Fin n) F4) :
    quadMat c (A * X * B) = A * quadMat c X * B := by
  have hBA' : ∀ Z : Matrix (Fin n) (Fin n) F4, B * (A * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  simp only [quadMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hBA', hAB]

theorem quadMat_transpose (c : F4) (X : Matrix (Fin n) (Fin n) F4) :
    quadMat c Xᵀ = (quadMat c X)ᵀ := by
  have hcomm : (X * X + c • X + 1) * (X - 1) = (X - 1) * (X * X + c • X + 1) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, smul_sub]
    abel
  rw [quadMat, quadMat, hcomm]
  simp only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.transpose_sub]

theorem quadMat_inv (c : F4) {X Y : Matrix (Fin n) (Fin n) F4} (hYX : Y * X = 1) :
    quadMat c Y = -(Y * Y * Y) * quadMat c X := by
  have hYX' : ∀ Z : Matrix (Fin n) (Fin n) F4, Y * (X * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hYX, Matrix.one_mul]
  simp only [quadMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.neg_mul, hYX', hYX,
    smul_neg]
  abel

theorem quadMat_blockMat (c : F4) {m i k : ℕ} (h : i + k ≤ m) (A : Matrix (Fin k) (Fin k) F4) :
    quadMat c (blockMat m i A) =
      blockSel F4 m k i * quadMat c A * (blockSel F4 m k i)ᵀ := by
  have hL := blockSel_transpose_mul_self (F := F4) h
  set L := blockSel F4 m k i with hLdef
  have hL' : ∀ Z : Matrix (Fin k) (Fin m) F4, Lᵀ * (L * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hL, Matrix.one_mul]
  obtain ⟨N, rfl⟩ : ∃ N : Matrix (Fin k) (Fin k) F4, A = 1 + N := ⟨A - 1, by abel⟩
  have hb : blockMat m i (1 + N) = 1 + L * N * Lᵀ := by
    rw [blockMat, add_sub_cancel_left]
  rw [hb]
  simp only [quadMat, add_sub_cancel_left, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hL']

theorem quadMat_conj_eq_zero_iff (c : F4) {A B : Matrix (Fin n) (Fin n) F4} (hAB : A * B = 1)
    (hBA : B * A = 1) (X : Matrix (Fin n) (Fin n) F4) :
    quadMat c (A * X * B) = 0 ↔ quadMat c X = 0 := by
  rw [quadMat_conj c hAB hBA]
  constructor
  · intro h
    have := congrArg (fun M => B * M * A) h
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc B A, hBA, Matrix.one_mul, hAB,
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul] using this
  · intro h
    rw [h, Matrix.mul_zero, Matrix.zero_mul]

theorem quadMat_transpose_eq_zero_iff (c : F4) (X : Matrix (Fin n) (Fin n) F4) :
    quadMat c Xᵀ = 0 ↔ quadMat c X = 0 := by
  rw [quadMat_transpose, Matrix.transpose_eq_zero]

theorem quadMat_inv_eq_zero_iff (c : F4) {X Y : Matrix (Fin n) (Fin n) F4} (hXY : X * Y = 1)
    (hYX : Y * X = 1) : quadMat c Y = 0 ↔ quadMat c X = 0 := by
  constructor
  · intro h
    rw [quadMat_inv c hXY, h, Matrix.mul_zero]
  · intro h
    rw [quadMat_inv c hYX, h, Matrix.mul_zero]

theorem quadMat_blockMat_eq_zero_iff (c : F4) {m i k : ℕ} (h : i + k ≤ m)
    (A : Matrix (Fin k) (Fin k) F4) : quadMat c (blockMat m i A) = 0 ↔ quadMat c A = 0 := by
  have hL := blockSel_transpose_mul_self (F := F4) h
  rw [quadMat_blockMat c h]
  constructor
  · intro h0
    have := congrArg (fun M => (blockSel F4 m k i)ᵀ * M * blockSel F4 m k i) h0
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc (blockSel F4 m k i)ᵀ (blockSel F4 m k i), hL,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul] using this
  · intro h0
    rw [h0, Matrix.mul_zero, Matrix.zero_mul]

theorem quadMat_conj_SL (c : F4) (g h : Matrix.SpecialLinearGroup (Fin n) F4) :
    quadMat c ((h * g * h⁻¹ : Matrix.SpecialLinearGroup (Fin n) F4) : Matrix (Fin n) (Fin n) F4) =
      0 ↔ quadMat c (g : Matrix (Fin n) (Fin n) F4) = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  refine quadMat_conj_eq_zero_iff c ?_ ?_ _
  · rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  · rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem quadMat_conj_GL (c : F4) (C : Matrix.GeneralLinearGroup (Fin n) F4)
    (X : Matrix (Fin n) (Fin n) F4) :
    quadMat c (C.val * X * (C⁻¹).val) = 0 ↔ quadMat c X = 0 :=
  quadMat_conj_eq_zero_iff c (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) X

theorem quadMat_invTranspose_SL (c : F4) (g : Matrix.SpecialLinearGroup (Fin n) F4) :
    quadMat c ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) F4) : Matrix (Fin n) (Fin n) F4)ᵀ = 0 ↔
      quadMat c (g : Matrix (Fin n) (Fin n) F4) = 0 := by
  rw [quadMat_transpose_eq_zero_iff]
  refine quadMat_inv_eq_zero_iff c ?_ ?_
  · rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  · rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem quadMat_blockSL (c : F4) {m k i : ℕ} (h : i + k ≤ m)
    (a : Matrix.SpecialLinearGroup (Fin k) F4) :
    quadMat c ((CFSG.ClassicalInvolution.WeakCT.blockSL F4 m k i h a :
      Matrix.SpecialLinearGroup (Fin m) F4) : Matrix (Fin m) (Fin m) F4) = 0 ↔
      quadMat c (a : Matrix (Fin k) (Fin k) F4) = 0 := by
  rw [CFSG.ClassicalInvolution.WeakCT.coe_blockSL]
  exact quadMat_blockMat_eq_zero_iff c h _

end CFSG.StandardType.N2Chart

end
