module

public import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofTensor
public import CFSG.Adapters.TauCetiExceptional.TwistedD4Block

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item223Rank2Proof

open Matrix CFSG.TauCetiBridge.Twisted

section Blocks

@[expose] def blk {R : Type*} (k : Fin 3) (M : Matrix (Fin 24) (Fin 24) R) :
    Matrix (Fin 8) (Fin 8) R :=
  M.submatrix (blkIdx k) (blkIdx k)

theorem blk_apply {R : Type*} (k : Fin 3) (M : Matrix (Fin 24) (Fin 24) R) (r c : Fin 8) :
    blk k M r c = M (blkIdx k r) (blkIdx k c) :=
  rfl

variable {R : Type*} [CommRing R]

theorem d4Blk_blkIdx (k : Fin 3) (r : Fin 8) : d4Blk (blkIdx k r) = k := by
  ext
  simp only [d4Blk, blkIdx]
  omega

theorem blkIdx_injective (k : Fin 3) : Function.Injective (blkIdx k) := by
  intro r r' h
  ext
  have := congrArg Fin.val h
  simp only [blkIdx] at this
  omega

theorem blkIdx_bijective : Function.Bijective fun p : Fin 3 × Fin 8 => blkIdx p.1 p.2 := by
  constructor
  · rintro ⟨k, r⟩ ⟨k', r'⟩ h
    have := congrArg Fin.val h
    simp only [blkIdx] at this
    have hk : (k : ℕ) = k' := by omega
    have hr : (r : ℕ) = r' := by omega
    exact Prod.ext (Fin.ext hk) (Fin.ext hr)
  · intro a
    refine ⟨(⟨(a : ℕ) / 8, by omega⟩, ⟨(a : ℕ) % 8, by omega⟩), ?_⟩
    ext
    simp only [blkIdx]
    omega

theorem sum_fin_twentyFour {M : Type*} [AddCommMonoid M] (f : Fin 24 → M) :
    ∑ a, f a = ∑ k : Fin 3, ∑ r : Fin 8, f (blkIdx k r) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ blkIdx_bijective _ _ fun _ => rfl).symm

theorem blk_mul {M : Matrix (Fin 24) (Fin 24) R} (hM : IsBlockDiag d4Blk R M)
    (N : Matrix (Fin 24) (Fin 24) R) (k : Fin 3) : blk k (M * N) = blk k M * blk k N := by
  ext r c
  rw [blk_apply, Matrix.mul_apply, sum_fin_twentyFour, Finset.sum_eq_single k]
  · rfl
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun r' _ => ?_
    rw [hM _ _ (by rw [d4Blk_blkIdx, d4Blk_blkIdx]; exact Ne.symm hk'), zero_mul]
  · simp

theorem blk_one (k : Fin 3) : blk k (1 : Matrix (Fin 24) (Fin 24) R) = 1 := by
  ext r c
  by_cases h : r = c
  · subst h
    simp [blk_apply]
  · rw [blk_apply, Matrix.one_apply_ne ((blkIdx_injective k).ne h), Matrix.one_apply_ne h]

theorem blk_add (k : Fin 3) (M N : Matrix (Fin 24) (Fin 24) R) :
    blk k (M + N) = blk k M + blk k N :=
  rfl

theorem blk_smul (k : Fin 3) (c : R) (M : Matrix (Fin 24) (Fin 24) R) :
    blk k (c • M) = c • blk k M :=
  rfl

@[expose] def castM {n : ℕ} : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) R :=
  (Int.castRingHom R).mapMatrix

theorem castM_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (r c : Fin n) :
    (castM A : Matrix (Fin n) (Fin n) R) r c = (A r c : R) :=
  rfl

theorem blk_castM (k : Fin 3) (M : Matrix (Fin 24) (Fin 24) ℤ) :
    blk k (castM M : Matrix (Fin 24) (Fin 24) R) = castM (blk k M) :=
  rfl

end Blocks

section Combination

variable {R : Type*} [CommRing R]

@[expose] def lcMu (A : Matrix (Fin 8) (Fin 8) R) (a : Fin 8) : Matrix (Fin 8) (Fin 8) R :=
  ∑ b, A b a • castM (muMat b)

@[expose] def lcNu (A : Matrix (Fin 8) (Fin 8) R) (a : Fin 8) : Matrix (Fin 8) (Fin 8) R :=
  ∑ b, A b a • castM (nuMat b)

theorem lcMu_one (a : Fin 8) : lcMu (1 : Matrix (Fin 8) (Fin 8) R) a =
    castM (muMat a) := by
  simp [lcMu, Matrix.one_apply]

theorem lcNu_one (a : Fin 8) : lcNu (1 : Matrix (Fin 8) (Fin 8) R) a =
    castM (nuMat a) := by
  simp [lcNu, Matrix.one_apply]

theorem lcMu_add (A A' : Matrix (Fin 8) (Fin 8) R) (a : Fin 8) :
    lcMu (A + A') a = lcMu A a + lcMu A' a := by
  simp [lcMu, add_smul, Finset.sum_add_distrib]

theorem lcNu_add (A A' : Matrix (Fin 8) (Fin 8) R) (a : Fin 8) :
    lcNu (A + A') a = lcNu A a + lcNu A' a := by
  simp [lcNu, add_smul, Finset.sum_add_distrib]

theorem lcMu_smul (c : R) (A : Matrix (Fin 8) (Fin 8) R) (a : Fin 8) :
    lcMu (c • A) a = c • lcMu A a := by
  simp [lcMu, Finset.smul_sum, smul_smul]

theorem lcNu_smul (c : R) (A : Matrix (Fin 8) (Fin 8) R) (a : Fin 8) :
    lcNu (c • A) a = c • lcNu A a := by
  simp [lcNu, Finset.smul_sum, smul_smul]

theorem lcMu_mul (A A' : Matrix (Fin 8) (Fin 8) R) (a : Fin 8) :
    lcMu (A * A') a = ∑ b, A' b a • lcMu A b := by
  simp only [lcMu, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem lcNu_mul (A A' : Matrix (Fin 8) (Fin 8) R) (a : Fin 8) :
    lcNu (A * A') a = ∑ b, A' b a • lcNu A b := by
  simp only [lcNu, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem castM_sum_smul_muMat (A : Matrix (Fin 8) (Fin 8) ℤ) (a : Fin 8) :
    (castM (∑ b, A b a • muMat b) : Matrix (Fin 8) (Fin 8) R) = lcMu (castM A) a := by
  rw [lcMu, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_zsmul, castM_apply, Int.cast_smul_eq_zsmul]

theorem castM_sum_smul_nuMat (A : Matrix (Fin 8) (Fin 8) ℤ) (a : Fin 8) :
    (castM (∑ b, A b a • nuMat b) : Matrix (Fin 8) (Fin 8) R) = lcNu (castM A) a := by
  rw [lcNu, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_zsmul, castM_apply, Int.cast_smul_eq_zsmul]

end Combination

section CliffEq

variable {R : Type*} [CommRing R]

@[expose] def CliffEq (M : Matrix (Fin 24) (Fin 24) R) : Prop :=
  ∀ a, blk 2 M * castM (muMat a) = lcMu (blk 0 M) a * blk 1 M ∧
    blk 1 M * castM (nuMat a) = lcNu (blk 0 M) a * blk 2 M

theorem CliffEq.mul_lcMu {M : Matrix (Fin 24) (Fin 24) R} (hM : CliffEq M)
    (A : Matrix (Fin 8) (Fin 8) R) (a : Fin 8) :
    blk 2 M * lcMu A a = lcMu (blk 0 M * A) a * blk 1 M := by
  rw [lcMu, Matrix.mul_sum, lcMu_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_smul, (hM b).1, smul_mul_assoc]

theorem CliffEq.mul_lcNu {M : Matrix (Fin 24) (Fin 24) R} (hM : CliffEq M)
    (A : Matrix (Fin 8) (Fin 8) R) (a : Fin 8) :
    blk 1 M * lcNu A a = lcNu (blk 0 M * A) a * blk 2 M := by
  rw [lcNu, Matrix.mul_sum, lcNu_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_smul, (hM b).2, smul_mul_assoc]

theorem cliffEq_one : CliffEq (1 : Matrix (Fin 24) (Fin 24) R) := fun a => by
  simp only [blk_one, lcMu_one, lcNu_one, Matrix.one_mul, Matrix.mul_one]
  exact ⟨trivial, trivial⟩

theorem CliffEq.mul {M N : Matrix (Fin 24) (Fin 24) R} (hMb : IsBlockDiag d4Blk R M)
    (hM : CliffEq M) (hN : CliffEq N) : CliffEq (M * N) := by
  intro a
  constructor
  · rw [blk_mul hMb, blk_mul hMb, blk_mul hMb, Matrix.mul_assoc, (hN a).1, ← Matrix.mul_assoc,
      hM.mul_lcMu, Matrix.mul_assoc]
  · rw [blk_mul hMb, blk_mul hMb, blk_mul hMb, Matrix.mul_assoc, (hN a).2, ← Matrix.mul_assoc,
      hM.mul_lcNu, Matrix.mul_assoc]

theorem one_add_smul_mul_eq {A : Type*} [Ring A] [Algebra R A] (c : R) (P Q m : A)
    (h : (P * m - m * Q) * Q = 0) :
    (1 + c • P) * m = (m + c • (P * m - m * Q)) * (1 + c • Q) := by
  have e : (m + c • (P * m - m * Q)) * (1 + c • Q) =
      (1 + c • P) * m + (c * c) • ((P * m - m * Q) * Q) := by
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
      sub_mul, smul_sub, smul_add]
    abel
  rw [e, h, smul_zero, add_zero]

theorem cliffEq_one_add_smul {X : Matrix (Fin 24) (Fin 24) ℤ}
    (hd1 : ∀ a, blk 2 X * muMat a - muMat a * blk 1 X = ∑ b, blk 0 X b a • muMat b)
    (hd2 : ∀ a, (∑ b, blk 0 X b a • muMat b) * blk 1 X = 0)
    (hd3 : ∀ a, blk 1 X * nuMat a - nuMat a * blk 2 X = ∑ b, blk 0 X b a • nuMat b)
    (hd4 : ∀ a, (∑ b, blk 0 X b a • nuMat b) * blk 2 X = 0) (c : R) :
    CliffEq (1 + c • (castM X : Matrix (Fin 24) (Fin 24) R)) := by
  intro a
  have hY : ∀ k, blk k (1 + c • (castM X : Matrix (Fin 24) (Fin 24) R)) =
      1 + c • castM (blk k X) := fun k => by
    rw [blk_add, blk_one, blk_smul, blk_castM]
  have h1 := congrArg (castM (R := R)) (hd1 a)
  have h2 := congrArg (castM (R := R)) (hd2 a)
  have h3 := congrArg (castM (R := R)) (hd3 a)
  have h4 := congrArg (castM (R := R)) (hd4 a)
  rw [map_sub, map_mul, map_mul, castM_sum_smul_muMat] at h1
  rw [map_mul, castM_sum_smul_muMat, map_zero] at h2
  rw [map_sub, map_mul, map_mul, castM_sum_smul_nuMat] at h3
  rw [map_mul, castM_sum_smul_nuMat, map_zero] at h4
  rw [hY, hY, hY, lcMu_add, lcMu_one, lcMu_smul, lcNu_add, lcNu_one, lcNu_smul, ← h1, ← h3]
  rw [← h1] at h2
  rw [← h3] at h4
  exact ⟨one_add_smul_mul_eq c _ _ _ h2, one_add_smul_mul_eq c _ _ _ h4⟩

end CliffEq

section Subgroup

variable (R : Type*) [CommRing R]

@[expose] def cliffGL : Subgroup (Matrix.GeneralLinearGroup (Fin 24) R) where
  carrier := {g | g ∈ blockGL d4Blk R ∧ CliffEq (g : Matrix (Fin 24) (Fin 24) R) ∧
    CliffEq ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 24) R) : Matrix (Fin 24) (Fin 24) R)}
  one_mem' := ⟨one_mem _, by rw [Units.val_one]; exact cliffEq_one,
    by rw [inv_one, Units.val_one]; exact cliffEq_one⟩
  mul_mem' {g h} hg hh := ⟨mul_mem hg.1 hh.1,
    by rw [Units.val_mul]; exact hg.2.1.mul hg.1.1 hh.2.1,
    by rw [_root_.mul_inv_rev, Units.val_mul]; exact hh.2.2.mul hh.1.2 hg.2.2⟩
  inv_mem' {g} hg := ⟨inv_mem hg.1, hg.2.2, by rw [inv_inv]; exact hg.2.1⟩

variable {R}

theorem raisingMatrix_isBlockDiag (i : Fin 4) :
    IsBlockDiag d4Blk ℤ (TauCeti.D4Tripled.raisingMatrix i) := fun a b hab => by
  rw [TauCeti.D4Tripled.raisingMatrix_apply]
  exact raising_isBlockDiag i a b hab

theorem loweringMatrix_isBlockDiag (i : Fin 4) :
    IsBlockDiag d4Blk ℤ (TauCeti.D4Tripled.loweringMatrix i) := fun a b hab => by
  rw [TauCeti.D4Tripled.loweringMatrix_apply]
  exact lowering_isBlockDiag i a b hab

theorem blk_raisingMatrix (i : Fin 4) (k : Fin 3) :
    blk k (TauCeti.D4Tripled.raisingMatrix i) = raiseBlk i k := by
  ext r c
  exact raisingMatrix_blkIdx i k r c

theorem blk_loweringMatrix (i : Fin 4) (k : Fin 3) :
    blk k (TauCeti.D4Tripled.loweringMatrix i) = lowerBlk i k := by
  ext r c
  exact loweringMatrix_blkIdx i k r c

theorem cliffEq_one_add_smul_raising (i : Fin 4) (c : R) :
    CliffEq (1 + c • (castM (TauCeti.D4Tripled.raisingMatrix i) :
      Matrix (Fin 24) (Fin 24) R)) :=
  cliffEq_one_add_smul (fun a => by simp only [blk_raisingMatrix]; exact mu_raise_check i a)
    (fun a => by simp only [blk_raisingMatrix]; exact mu_raise_sq_check i a)
    (fun a => by simp only [blk_raisingMatrix]; exact nu_raise_check i a)
    (fun a => by simp only [blk_raisingMatrix]; exact nu_raise_sq_check i a) c

theorem cliffEq_one_add_smul_lowering (i : Fin 4) (c : R) :
    CliffEq (1 + c • (castM (TauCeti.D4Tripled.loweringMatrix i) :
      Matrix (Fin 24) (Fin 24) R)) :=
  cliffEq_one_add_smul (fun a => by simp only [blk_loweringMatrix]; exact mu_lower_check i a)
    (fun a => by simp only [blk_loweringMatrix]; exact mu_lower_sq_check i a)
    (fun a => by simp only [blk_loweringMatrix]; exact nu_lower_check i a)
    (fun a => by simp only [blk_loweringMatrix]; exact nu_lower_sq_check i a) c

theorem mem_cliffGL_of {X : Matrix (Fin 24) (Fin 24) ℤ} (hX : IsBlockDiag d4Blk ℤ X)
    (hcl : ∀ c : R, CliffEq (1 + c • (castM X : Matrix (Fin 24) (Fin 24) R)))
    {g : Matrix.GeneralLinearGroup (Fin 24) R} {c : R}
    (hg : (g : Matrix (Fin 24) (Fin 24) R) = 1 + c • (castM X : Matrix (Fin 24) (Fin 24) R))
    (hg' : ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 24) R) : Matrix (Fin 24) (Fin 24) R) =
      1 + (-c) • (castM X : Matrix (Fin 24) (Fin 24) R)) : g ∈ cliffGL R :=
  ⟨mem_blockGL_of (hg ▸ one_add_smul_isBlockDiag c hX) (hg' ▸ one_add_smul_isBlockDiag (-c) hX),
    hg ▸ hcl c, hg' ▸ hcl (-c)⟩

end Subgroup

section Vectors

variable {R : Type*} [CommRing R]

@[expose] def muR (v s : Fin 8 → R) : Fin 8 → R :=
  ∑ a, v a • (castM (muMat a) *ᵥ s)

@[expose] def nuR (v u : Fin 8 → R) : Fin 8 → R :=
  ∑ a, v a • (castM (nuMat a) *ᵥ u)

theorem muR_smul_left (c : R) (v s : Fin 8 → R) : muR (c • v) s = c • muR v s := by
  simp [muR, Finset.smul_sum, smul_smul]

theorem muR_smul_right (c : R) (v s : Fin 8 → R) : muR v (c • s) = c • muR v s := by
  simp only [muR, Matrix.mulVec_smul, Finset.smul_sum, smul_comm c]

theorem nuR_smul_right (c : R) (v u : Fin 8 → R) : nuR v (c • u) = c • nuR v u := by
  simp only [nuR, Matrix.mulVec_smul, Finset.smul_sum, smul_comm c]

theorem sum_smul_mulVec (A : Fin 8 → Matrix (Fin 8) (Fin 8) R) (v w : Fin 8 → R) :
    ∑ a, v a • (A a *ᵥ w) = (∑ a, v a • A a) *ᵥ w := by
  rw [Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec]

theorem mulVec_muR {M : Matrix (Fin 24) (Fin 24) R} (hM : CliffEq M) (v s : Fin 8 → R) :
    blk 2 M *ᵥ muR v s = muR (blk 0 M *ᵥ v) (blk 1 M *ᵥ s) := by
  have key : ∀ a, blk 2 M *ᵥ (castM (muMat a) *ᵥ s) =
      ∑ b, blk 0 M b a • (castM (muMat b) *ᵥ (blk 1 M *ᵥ s)) := by
    intro a
    rw [Matrix.mulVec_mulVec, (hM a).1, ← Matrix.mulVec_mulVec, lcMu, sum_smul_mulVec]
  simp only [muR, Matrix.mulVec_sum, Matrix.mulVec_smul, key, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, mul_comm]

theorem mulVec_nuR {M : Matrix (Fin 24) (Fin 24) R} (hM : CliffEq M) (v u : Fin 8 → R) :
    blk 1 M *ᵥ nuR v u = nuR (blk 0 M *ᵥ v) (blk 2 M *ᵥ u) := by
  have key : ∀ a, blk 1 M *ᵥ (castM (nuMat a) *ᵥ u) =
      ∑ b, blk 0 M b a • (castM (nuMat b) *ᵥ (blk 2 M *ᵥ u)) := by
    intro a
    rw [Matrix.mulVec_mulVec, (hM a).2, ← Matrix.mulVec_mulVec, lcNu, sum_smul_mulVec]
  simp only [nuR, Matrix.mulVec_sum, Matrix.mulVec_smul, key, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, mul_comm]

theorem nuR_muR_add (v w s : Fin 8 → R) :
    nuR v (muR w s) + nuR w (muR v s) =
      (v ⬝ᵥ (castM formMat *ᵥ w)) • s := by
  have hcl : ∀ a b, castM (nuMat a) * castM (muMat b) +
      castM (nuMat b) * castM (muMat a) =
        ((formMat a b : ℤ) : R) • (1 : Matrix (Fin 8) (Fin 8) R) := by
    intro a b
    have h := congrArg (castM (R := R)) (clifford_check a b)
    rw [map_add, map_mul, map_mul, map_zsmul, map_one] at h
    rw [h, Int.cast_smul_eq_zsmul]
  have hexp : ∀ x y : Fin 8 → R, nuR x (muR y s) =
      ∑ a, ∑ b, (x a * y b) • ((castM (nuMat a) *
        castM (muMat b)) *ᵥ s) := by
    intro x y
    simp only [nuR, muR, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Finset.smul_sum, smul_smul]
  rw [hexp, hexp, Finset.sum_comm (f := fun a b => (w a * v b) • _), ← Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib]
  have hterm : ∀ a b, (v a * w b) • ((castM (nuMat a) *
      castM (muMat b)) *ᵥ s) + (w b * v a) • ((castM (nuMat b) *
      castM (muMat a)) *ᵥ s) = (v a * (formMat a b : R) * w b) • s := by
    intro a b
    rw [mul_comm (w b) (v a), ← smul_add, ← Matrix.add_mulVec, hcl, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul]
    ring_nf
  simp only [hterm, ← Finset.sum_smul]
  congr 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, castM_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem det_formMat_map_ne_zero [Nontrivial R] :
    (castM formMat : Matrix (Fin 8) (Fin 8) R).det ≠ 0 := by
  intro h
  have h1 := congrArg (fun A : Matrix (Fin 8) (Fin 8) ℤ =>
    (castM A : Matrix (Fin 8) (Fin 8) R).det) formMat_mul_self
  simp only [map_mul, Matrix.det_mul, h, mul_zero, map_one, Matrix.det_one] at h1
  exact zero_ne_one h1

end Vectors

end CFSG.RankThree.PartTwo.Sec21.Item223Rank2Proof
