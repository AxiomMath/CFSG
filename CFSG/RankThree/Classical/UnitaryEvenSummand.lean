module

public import CFSG.RankThree.Classical.SiegelRadical
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.RankThree.Classical

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

section Adjoint

variable {l m o : Type*} [Fintype m]

@[expose] noncomputable def hadj (A : Matrix l m K) : Matrix m l K :=
  (A.map h.bar)ᵀ

theorem hadj_mul (A : Matrix l m K) (B : Matrix m o K) : hadj h (A * B) = hadj h B * hadj h A := by
  rw [hadj, hadj, hadj, Matrix.map_mul, Matrix.transpose_mul]

omit [Fintype m] in
theorem hadj_hadj (A : Matrix l m K) : hadj h (hadj h A) = A := by
  ext i j
  simp [hadj, h.bar_bar]

omit [Fintype m] in
theorem hadj_fromBlocks {l' m' : Type*} (A : Matrix l m K) (B : Matrix l m' K)
    (C : Matrix l' m K) (D : Matrix l' m' K) :
    hadj h (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (hadj h A) (hadj h C) (hadj h B) (hadj h D) := by
  rw [hadj, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]
  rfl

omit [Fintype m] in
theorem hadj_zero : hadj h (0 : Matrix l m K) = 0 := by
  ext i j
  simp [hadj]

omit [Fintype m] in
theorem hadj_one [DecidableEq m] : hadj h (1 : Matrix m m K) = 1 := by
  ext i j
  simp [hadj, Matrix.one_apply, eq_comm]

end Adjoint

section Frame

variable {r m : ℕ}

@[expose] def frameGram (r m : ℕ) (K : Type) [Field K] :
    Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) ((Fin r ⊕ Fin r) ⊕ Fin m) K :=
  Matrix.fromBlocks (hypGram2 r K) 0 0 1

theorem frameGram_mul_self : frameGram r m K * frameGram r m K = 1 := by
  rw [frameGram, Matrix.fromBlocks_multiply, hypGram2, Matrix.fromBlocks_multiply]
  simp [← Matrix.fromBlocks_one]

theorem hadj_frameGram : hadj h (frameGram r m K) = frameGram r m K := by
  simp only [frameGram, hadj_fromBlocks, hypGram2, hadj_one, hadj_zero]

@[expose] def frameMat (m : ℕ) (B : Matrix (Fin r) (Fin r) K) :
    Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) ((Fin r ⊕ Fin r) ⊕ Fin m) K :=
  Matrix.fromBlocks (siegelMat B) 0 0 1

theorem frameMat_mul (B B' : Matrix (Fin r) (Fin r) K) :
    frameMat m B * frameMat m B' = frameMat m (B + B') := by
  rw [frameMat, frameMat, frameMat, Matrix.fromBlocks_multiply, siegelMat_mul]
  simp

theorem frameMat_zero : frameMat m (0 : Matrix (Fin r) (Fin r) K) = 1 := by
  rw [frameMat, siegelMat_zero, Matrix.fromBlocks_one]

theorem siegelMat_isometry {B : Matrix (Fin r) (Fin r) K} (hB : B ∈ skewHermMatrices h r) :
    hadj h (siegelMat B) * hypGram2 r K * siegelMat B = hypGram2 r K := by
  have hB' : B + hadj h B = 0 := hB
  rw [siegelMat, hadj_fromBlocks, hadj_one, hadj_zero, hypGram2, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [add_comm, hB']

theorem frameMat_isometry {B : Matrix (Fin r) (Fin r) K} (hB : B ∈ skewHermMatrices h r) :
    hadj h (frameMat m B) * frameGram r m K * frameMat m B = frameGram r m K := by
  rw [frameMat, frameGram, hadj_fromBlocks, hadj_one, hadj_zero, hadj_zero,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [siegelMat_isometry h hB]

theorem det_frameMat (B : Matrix (Fin r) (Fin r) K) : (frameMat m B).det = 1 := by
  rw [frameMat, Matrix.det_fromBlocks_zero₂₁, siegelMat, Matrix.det_fromBlocks_zero₂₁]
  simp

end Frame

section Radical

variable {n r m : ℕ}

@[expose] def frameRadical (P : Matrix (Fin n) ((Fin r ⊕ Fin r) ⊕ Fin m) K) :
    Subgroup (unitarySU p f K n) where
  carrier := {g | ∃ B ∈ skewHermMatrices h r,
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P = P * frameMat m B}
  mul_mem' {g g'} hg hg' := by
    obtain ⟨B, hB, hgB⟩ := hg
    obtain ⟨B', hB', hgB'⟩ := hg'
    refine ⟨B + B', (skewHermMatrices h r).add_mem hB hB', ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, hgB', ← Matrix.mul_assoc, hgB,
      Matrix.mul_assoc, frameMat_mul]
  one_mem' := ⟨0, (skewHermMatrices h r).zero_mem, by
    rw [frameMat_zero, Matrix.mul_one, Subgroup.coe_one, Units.val_one, Matrix.one_mul]⟩
  inv_mem' {g} hg := by
    obtain ⟨B, hB, hgB⟩ := hg
    refine ⟨-B, (skewHermMatrices h r).neg_mem hB, ?_⟩
    have hinv : ((g⁻¹ : unitarySU p f K n) : GL (Fin n) K).val *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((g⁻¹ : unitarySU p f K n) : GL (Fin n) K).val * P
        = ((g⁻¹ : unitarySU p f K n) : GL (Fin n) K).val * (P * frameMat m B) *
            frameMat m (-B) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, frameMat_mul, add_neg_cancel, frameMat_zero,
            Matrix.mul_one]
      _ = P * frameMat m (-B) := by
          rw [← hgB, ← Matrix.mul_assoc, hinv, Matrix.one_mul]

@[expose] def frameUnipotent (P : Matrix (Fin n) ((Fin r ⊕ Fin r) ⊕ Fin m) K) :
    Subgroup (unitaryPSU h n) :=
  (frameRadical h P).map (unitaryProj h n)

variable {P : Matrix (Fin n) ((Fin r ⊕ Fin r) ⊕ Fin m) K}
  (hP : hadj h P * P = frameGram r m K) (hnm : 2 * r + m = n)

include hP hnm in
theorem frame_mul_inv : P * (frameGram r m K * hadj h P) = 1 := by
  have hleft : frameGram r m K * hadj h P * P = 1 := by
    rw [Matrix.mul_assoc, hP, frameGram_mul_self]
  have e : (Fin r ⊕ Fin r) ⊕ Fin m ≃ Fin n :=
    Fintype.equivOfCardEq (by simp [Fintype.card_sum]; omega)
  exact (Matrix.mul_eq_one_comm_of_equiv e).mp hleft

include hP in
theorem frame_inv_mul : frameGram r m K * hadj h P * P = 1 := by
  rw [Matrix.mul_assoc, hP, frameGram_mul_self]

@[expose] noncomputable def frameConj (P : Matrix (Fin n) ((Fin r ⊕ Fin r) ⊕ Fin m) K)
    (T : Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) ((Fin r ⊕ Fin r) ⊕ Fin m) K) :
    Matrix (Fin n) (Fin n) K :=
  P * T * (frameGram r m K * hadj h P)

include hP in
theorem frameConj_mul (T T' : Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) ((Fin r ⊕ Fin r) ⊕ Fin m) K) :
    frameConj h P T * frameConj h P T' = frameConj h P (T * T') := by
  rw [frameConj, frameConj, frameConj]
  calc P * T * (frameGram r m K * hadj h P) * (P * T' * (frameGram r m K * hadj h P))
      = P * T * (frameGram r m K * hadj h P * P) * T' * (frameGram r m K * hadj h P) := by
        simp only [Matrix.mul_assoc]
    _ = P * (T * T') * (frameGram r m K * hadj h P) := by
        rw [frame_inv_mul h hP, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

include hP hnm in
theorem frameConj_one : frameConj h P 1 = 1 := by
  rw [frameConj, Matrix.mul_one, frame_mul_inv h hP hnm]

include hP in
theorem frameConj_mul_frame (T : Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) ((Fin r ⊕ Fin r) ⊕ Fin m) K) :
    frameConj h P T * P = P * T := by
  rw [frameConj, Matrix.mul_assoc, frame_inv_mul h hP, Matrix.mul_one]

include hP hnm in
theorem hadj_frameConj_mul
    {T : Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) ((Fin r ⊕ Fin r) ⊕ Fin m) K}
    (hT : hadj h T * frameGram r m K * T = frameGram r m K) :
    hadj h (frameConj h P T) * frameConj h P T = 1 := by
  rw [frameConj, hadj_mul, hadj_mul, hadj_mul, hadj_hadj, hadj_frameGram]
  calc P * frameGram r m K * (hadj h T * hadj h P) * (P * T * (frameGram r m K * hadj h P))
      = P * frameGram r m K * (hadj h T * (hadj h P * P) * T) * frameGram r m K * hadj h P := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hP, hT]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (frameGram r m K) (frameGram r m K), frameGram_mul_self,
          Matrix.one_mul, frame_mul_inv h hP hnm]

include hP hnm in
theorem det_frameConj (T : Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) ((Fin r ⊕ Fin r) ⊕ Fin m) K) :
    (frameConj h P T).det = T.det := by
  have e : (Fin r ⊕ Fin r) ⊕ Fin m ≃ Fin n :=
    Fintype.equivOfCardEq (by simp [Fintype.card_sum]; omega)
  set Q := frameGram r m K * hadj h P
  have hPQ : P * Q = 1 := frame_mul_inv h hP hnm
  have hsplit : frameConj h P T =
      P.submatrix id e.symm * T.submatrix e.symm e.symm * Q.submatrix e.symm id := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl
  have hPQ' : P.submatrix id e.symm * Q.submatrix e.symm id = 1 := by
    rw [Matrix.submatrix_mul_equiv, hPQ, Matrix.submatrix_id_id]
  rw [hsplit, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, mul_comm _ T.det,
    mul_assoc, ← Matrix.det_mul, hPQ', Matrix.det_one, mul_one]

include hP in
theorem eq_smul_of_frameConj_eq_scalar
    {T : Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) ((Fin r ⊕ Fin r) ⊕ Fin m) K} {c : K}
    (hT : frameConj h P T = Matrix.scalar (Fin n) c) : T = c • 1 := by
  have := congrArg (fun A => frameGram r m K * hadj h P * A * P) hT
  simp only [frameConj] at this
  calc T = frameGram r m K * hadj h P * P * T * (frameGram r m K * hadj h P * P) := by
        rw [frame_inv_mul h hP, Matrix.one_mul, Matrix.mul_one]
    _ = frameGram r m K * hadj h P * (P * T * (frameGram r m K * hadj h P)) * P := by
        simp only [Matrix.mul_assoc]
    _ = c • 1 := by
        rw [this, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
          Matrix.mul_one, Matrix.smul_mul, frame_inv_mul h hP]

@[expose] noncomputable def frameSU
    (T : Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) ((Fin r ⊕ Fin r) ⊕ Fin m) K)
    (hT : hadj h T * frameGram r m K * T = frameGram r m K) (hdet : T.det = 1) :
    unitarySU p f K n :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (frameConj h P T)
      (by rw [det_frameConj h hP hnm, hdet]; exact one_ne_zero),
    (mem_unitarySU_iff h).mpr ⟨by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      det_frameConj h hP hnm, hdet], hadj_frameConj_mul h hP hnm hT⟩⟩

theorem coe_frameSU (T : Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) ((Fin r ⊕ Fin r) ⊕ Fin m) K)
    (hT : hadj h T * frameGram r m K * T = frameGram r m K) (hdet : T.det = 1) :
    ((frameSU h hP hnm T hT hdet : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      frameConj h P T :=
  rfl

@[expose] noncomputable def frameSUHom :
    Multiplicative (skewHermMatrices h r) →* unitarySU p f K n where
  toFun B := frameSU h hP hnm (frameMat m (B.toAdd : Matrix (Fin r) (Fin r) K))
    (frameMat_isometry h B.toAdd.2) (det_frameMat _)
  map_one' := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_one, Units.val_one, coe_frameSU]
    change frameConj h P (frameMat m 0) = 1
    rw [frameMat_zero, frameConj_one h hP hnm]))
  map_mul' B B' := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_frameSU, coe_frameSU, coe_frameSU,
      frameConj_mul h hP, frameMat_mul]
    rfl))

theorem coe_frameSUHom (B : Multiplicative (skewHermMatrices h r)) :
    ((frameSUHom h hP hnm B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      frameConj h P (frameMat m (B.toAdd : Matrix (Fin r) (Fin r) K)) :=
  rfl

theorem frameRadical_eq_range : frameRadical h P = (frameSUHom h hP hnm).range := by
  ext g
  constructor
  · rintro ⟨B, hB, hgB⟩
    refine ⟨Multiplicative.ofAdd ⟨B, hB⟩, Subtype.ext (Units.ext ?_)⟩
    change frameConj h P (frameMat m B) = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [frameConj, ← hgB, Matrix.mul_assoc, frame_mul_inv h hP hnm, Matrix.mul_one]
  · rintro ⟨B, rfl⟩
    exact ⟨B.toAdd, B.toAdd.2, frameConj_mul_frame h hP _⟩

@[expose] noncomputable def frameUnipotentHom :
    Multiplicative (skewHermMatrices h r) →* unitaryPSU h n :=
  (unitaryProj h n).comp (frameSUHom h hP hnm)

theorem frameUnipotent_eq_range : frameUnipotent h P = (frameUnipotentHom h hP hnm).range := by
  rw [frameUnipotent, frameRadical_eq_range h hP hnm, MonoidHom.map_range]
  rfl

theorem frameUnipotentHom_injective : Function.Injective (frameUnipotentHom h hP hnm) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  have hmem : frameSUHom h hP hnm B ∈ unitaryScalars h n := by
    rw [← ker_unitaryProj]
    exact hB
  obtain ⟨c, -, -, hc⟩ := hmem
  have hT := eq_smul_of_frameConj_eq_scalar h hP (T := frameMat m
    (B.toAdd : Matrix (Fin r) (Fin r) K)) (c := (c : K)) (by
      rw [← coe_frameSU h hP hnm _ (frameMat_isometry h B.toAdd.2) (det_frameMat _)]
      change (((frameSUHom h hP hnm B : unitarySU p f K n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = _
      rw [hc, Matrix.GeneralLinearGroup.coe_scalar])
  have h12 := congrArg (fun A => (A.toBlocks₁₁).toBlocks₁₂) hT
  simp only [frameMat, siegelMat, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂] at h12
  have h0 : (B.toAdd : Matrix (Fin r) (Fin r) K) = 0 := by
    rw [h12]
    ext i j
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]
  exact Multiplicative.toAdd.injective (Subtype.ext h0)

end Radical

section Torus

variable {r m : ℕ}

@[expose] noncomputable def frameTorus (k₀ : Fin m) (c : K) :
    Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) ((Fin r ⊕ Fin r) ⊕ Fin m) K :=
  Matrix.fromBlocks (Matrix.fromBlocks (c • 1) 0 0 ((h.bar c)⁻¹ • 1)) 0 0
    (Matrix.diagonal (Function.update (1 : Fin m → K) k₀ ((h.bar c / c) ^ r)))

theorem frameTorus_isometry (k₀ : Fin m) {c : K} (hc : c ≠ 0) :
    hadj h (frameTorus h (r := r) k₀ c) * frameGram r m K * frameTorus h k₀ c =
      frameGram r m K := by
  have hbc : h.bar c ≠ 0 := (h.bar_eq_zero_iff).not.mpr hc
  have hd : h.bar ((h.bar c / c) ^ r) * (h.bar c / c) ^ r = 1 := by
    rw [map_pow, map_div₀, h.bar_bar, ← mul_pow, div_mul_div_comm, mul_comm c, div_self
      (mul_ne_zero hbc hc), one_pow]
  have hdiag : hadj h (Matrix.diagonal (Function.update (1 : Fin m → K) k₀ ((h.bar c / c) ^ r))) *
      Matrix.diagonal (Function.update (1 : Fin m → K) k₀ ((h.bar c / c) ^ r)) = 1 := by
    rw [hadj, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    simp only [Function.update_apply, Pi.one_apply]
    split_ifs
    · exact hd
    · simp
  have hs : ∀ (x : K), hadj h (x • (1 : Matrix (Fin r) (Fin r) K)) =
      h.bar x • (1 : Matrix (Fin r) (Fin r) K) := fun x => by
    ext i j
    simp [hadj, Matrix.one_apply, apply_ite h.bar, eq_comm]
  simp only [frameTorus, frameGram, hadj_fromBlocks, hadj_zero, hs, hypGram2,
    Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.mul_smul, smul_smul, hdiag, smul_zero]
  rw [inv_mul_cancel₀ hbc, map_inv₀, h.bar_bar, mul_inv_cancel₀ hc, one_smul]

theorem det_frameTorus (k₀ : Fin m) {c : K} (hc : c ≠ 0) :
    (frameTorus h (r := r) k₀ c).det = 1 := by
  have hbc : h.bar c ≠ 0 := (h.bar_eq_zero_iff).not.mpr hc
  rw [frameTorus, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul,
    Matrix.det_smul, Matrix.det_one, Matrix.det_diagonal,
    Finset.prod_update_of_mem (Finset.mem_univ k₀)]
  simp only [Fintype.card_fin, mul_one, Pi.one_apply, Finset.prod_const_one]
  rw [div_pow, inv_pow]
  field_simp

theorem frameTorus_mul_frameMat (k₀ : Fin m) {c : K} (hc : c ≠ 0)
    (B : Matrix (Fin r) (Fin r) K) :
    frameTorus h k₀ c * frameMat m B = frameMat m (h.norm c • B) * frameTorus h k₀ c := by
  have hbc : h.bar c ≠ 0 := (h.bar_eq_zero_iff).not.mpr hc
  simp only [frameTorus, frameMat, siegelMat, Matrix.fromBlocks_multiply, Matrix.mul_one,
    Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, smul_zero]
  congr 3
  rw [UnitaryFieldData.norm]
  field_simp

end Torus

section Scaling

variable {n r m : ℕ} {P : Matrix (Fin n) ((Fin r ⊕ Fin r) ⊕ Fin m) K}
  (hP : hadj h P * P = frameGram r m K) (hnm : 2 * r + m = n)

theorem frameUnipotentHom_conj (k₀ : Fin m) {c : K} (hc0 : c ≠ 0) (hc : h.norm c = 2)
    (v : skewHermMatrices h r) :
    unitaryProj h n (frameSU h hP hnm (frameTorus h (r := r) k₀ c)
        (frameTorus_isometry h k₀ hc0) (det_frameTorus h k₀ hc0)) *
      frameUnipotentHom h hP hnm (Multiplicative.ofAdd v) *
      (unitaryProj h n (frameSU h hP hnm (frameTorus h (r := r) k₀ c)
        (frameTorus_isometry h k₀ hc0) (det_frameTorus h k₀ hc0)))⁻¹ =
    frameUnipotentHom h hP hnm (Multiplicative.ofAdd (2 • v)) := by
  have hSU : frameSU h hP hnm (frameTorus h (r := r) k₀ c) (frameTorus_isometry h k₀ hc0)
        (det_frameTorus h k₀ hc0) * frameSUHom h hP hnm (Multiplicative.ofAdd v) =
      frameSUHom h hP hnm (Multiplicative.ofAdd (2 • v)) *
        frameSU h hP hnm (frameTorus h (r := r) k₀ c) (frameTorus_isometry h k₀ hc0)
          (det_frameTorus h k₀ hc0) := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_frameSUHom,
      coe_frameSUHom, coe_frameSU, frameConj_mul h hP, frameConj_mul h hP,
      frameTorus_mul_frameMat h k₀ hc0, hc]
    congr 3
    rw [toAdd_ofAdd, toAdd_ofAdd, AddSubgroup.coe_nsmul, two_smul, two_nsmul]
  rw [frameUnipotentHom, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul, ← map_inv,
    ← map_mul, hSU, mul_inv_cancel_right]

end Scaling

section Main

variable {n r : ℕ}

theorem unitary_even_summand_unipotent (hn : 2 * r < n)
    (P : Matrix (Fin n) ((Fin r ⊕ Fin r) ⊕ Fin (n - 2 * r)) K)
    (hP : (P.map h.bar)ᵀ * P = Matrix.fromBlocks (Matrix.fromBlocks 0 1 1 0) 0 0 1) :
    IsElemAbelian p (frameUnipotent h P) ∧ Nat.card (frameUnipotent h P) = p ^ (f * r ^ 2) := by
  have hP' : hadj h P * P = frameGram r (n - 2 * r) K := hP
  have hnm : 2 * r + (n - 2 * r) = n := by omega
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  rw [frameUnipotent_eq_range h hP' hnm]
  refine ⟨isElemAbelian_range (nsmul_char_eq_zero _) _, ?_⟩
  rw [MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (frameUnipotentHom_injective h hP' hnm), Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, card_skewHermMatrices, ← pow_mul]

theorem unitary_even_summand_unipotent_preimage_comm (hp3 : 3 < p) (hn : 2 * r < n)
    (P : Matrix (Fin n) ((Fin r ⊕ Fin r) ⊕ Fin (n - 2 * r)) K)
    (hP : (P.map h.bar)ᵀ * P = Matrix.fromBlocks (Matrix.fromBlocks 0 1 1 0) 0 0 1)
    {Y : Type*} [Group Y] (φ : Y →* unitaryPSU h n) (hφ : Function.Surjective φ)
    (hZ : φ.ker ≤ Subgroup.center Y) :
    ∀ x ∈ (frameUnipotent h P).comap φ, ∀ y ∈ (frameUnipotent h P).comap φ, x * y = y * x := by
  have hP' : hadj h P * P = frameGram r (n - 2 * r) K := hP
  have hnm : 2 * r + (n - 2 * r) = n := by omega
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  obtain ⟨c, hc⟩ : ∃ c : K, h.norm c = 2 := by
    obtain ⟨c, hc⟩ := h.normHom_surjective (2 : h.fixedField)
    refine ⟨c, ?_⟩
    have := congrArg Subtype.val hc
    rwa [UnitaryFieldData.coe_normHom] at this
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [UnitaryFieldData.norm, zero_mul] at hc
    exact h2 hc.symm
  have hconj := frameUnipotentHom_conj h hP' hnm (⟨0, by omega⟩ : Fin (n - 2 * r)) hc0 hc
  have hcop : ¬ p ∣ 2 * 2 - 1 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hvanish : ∀ v w, liftPair hφ (frameUnipotentHom h hP' hnm) v w = 1 := fun v w =>
    liftPair_eq_one_of_weight hφ _ hZ h.prime (nsmul_char_eq_zero _ v) (s := 2) (t := 2)
      (by norm_num) hcop (liftPair_conj' hφ _ hZ _ (hconj v) (hconj w))
  have hrange := frameUnipotent_eq_range h hP' hnm
  intro x hx y hy
  refine mul_comm_of_liftPair_eq_one hφ _ hZ hvanish ?_ ?_
  · rw [← hrange]
    exact hx
  · rw [← hrange]
    exact hy

end Main

end CFSG.RankThree.Classical
