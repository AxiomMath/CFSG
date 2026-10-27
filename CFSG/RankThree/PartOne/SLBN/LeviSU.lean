module

public import CFSG.RankThree.Classical.UnitaryEvenSummand

public section

namespace CFSG.RankThree.PartOne.SLBN

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {m : ℕ}

@[expose] noncomputable def leviSL (A : SL(2, K)) :
    Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin m) ((Fin 2 ⊕ Fin 2) ⊕ Fin m) K :=
  Matrix.fromBlocks (Matrix.fromBlocks (A : Matrix (Fin 2) (Fin 2) K) 0 0
    (hadj h ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K))) 0 0 1

theorem leviSL_mul (A B : SL(2, K)) :
    leviSL h (m := m) A * leviSL h B = leviSL h (A * B) := by
  simp only [leviSL, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_one, mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, hadj_mul]

theorem leviSL_isometry (A : SL(2, K)) :
    hadj h (leviSL h (m := m) A) * frameGram 2 m K * leviSL h A = frameGram 2 m K := by
  have h2 : ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    rfl
  have h1 : hadj h (A : Matrix (Fin 2) (Fin 2) K) *
      hadj h ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← hadj_mul, h2, hadj_one]
  simp only [leviSL, frameGram, hypGram2, hadj_fromBlocks, hadj_hadj, hadj_zero, hadj_one,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    add_zero, zero_add, h1, h2]

theorem det_leviSL (A : SL(2, K)) : (leviSL h (m := m) A).det = 1 := by
  rw [leviSL, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    Matrix.SpecialLinearGroup.det_coe, one_mul, hadj, Matrix.det_transpose,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]


theorem leviSL_one : leviSL h (m := m) (1 : SL(2, K)) = 1 := by
  simp [leviSL, hadj_one, Matrix.fromBlocks_one]

section Hom

variable {n : ℕ} {P : Matrix (Fin n) ((Fin 2 ⊕ Fin 2) ⊕ Fin m) K}
  (hP : hadj h P * P = frameGram 2 m K) (hnm : 2 * 2 + m = n)

@[expose] noncomputable def levSU : SL(2, K) →* unitarySU p f K n where
  toFun A := frameSU h hP hnm (leviSL h A) (leviSL_isometry h A) (det_leviSL h A)
  map_one' := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_one, Units.val_one, coe_frameSU]
    change frameConj h P (leviSL h 1) = 1
    rw [leviSL_one, frameConj_one h hP hnm]))
  map_mul' A B := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_frameSU, coe_frameSU, coe_frameSU,
      frameConj_mul h hP, leviSL_mul]))

theorem coe_levSU (A : SL(2, K)) :
    ((levSU h hP hnm A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      frameConj h P (leviSL h A) :=
  rfl

end Hom

@[expose] def invT (c c' : K) : Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin m) ((Fin 2 ⊕ Fin 2) ⊕ Fin m) K :=
  Matrix.fromBlocks (Matrix.fromBlocks (c • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0
    (c' • (1 : Matrix (Fin 2) (Fin 2) K))) 0 0 1

theorem invT_isometry {i : K} (hi : h.bar i = i) (hii : i * i = -1) :
    hadj h (invT (m := m) i (-i)) * frameGram 2 m K * invT i (-i) = frameGram 2 m K := by
  have hs : ∀ x : K, hadj h (x • (1 : Matrix (Fin 2) (Fin 2) K)) =
      h.bar x • (1 : Matrix (Fin 2) (Fin 2) K) := fun x => by
    ext a b
    simp [hadj, Matrix.one_apply, apply_ite h.bar, eq_comm]
  have e1 : -i * i = 1 := by rw [neg_mul, hii, neg_neg]
  have e2 : i * -i = 1 := by rw [mul_neg, hii, neg_neg]
  simp only [invT, frameGram, hypGram2, hadj_fromBlocks, hadj_zero, hadj_one, hs, map_neg, hi,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero,
    zero_add, Matrix.mul_smul, smul_smul, e1, e2, smul_zero, one_smul]

theorem det_invT {i : K} (hii : i * i = -1) : (invT (m := m) i (-i)).det = 1 := by
  rw [invT, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    Matrix.det_smul, Matrix.det_smul, Matrix.det_one]
  simp only [Fintype.card_fin, mul_one]
  linear_combination (i ^ 2 - 1) * hii


theorem invT_sq {i : K} (hii : i * i = -1) : invT (m := 0) i (-i) * invT i (-i) = -1 := by
  have e1 : (i * i) • (1 : Matrix (Fin 2) (Fin 2) K) = -1 := by rw [hii, neg_smul, one_smul]
  have e2 : (-i * -i) • (1 : Matrix (Fin 2) (Fin 2) K) = -1 := by
    rw [neg_mul_neg, hii, neg_smul, one_smul]
  have h0 : (-1 : Matrix (Fin 0) (Fin 0) K) = 1 := Subsingleton.elim _ _
  have h1 : (-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.fromBlocks (-1) 0 0 (-1) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have hneg : (-1 : Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) K) =
      Matrix.fromBlocks (Matrix.fromBlocks (-1) 0 0 (-1)) 0 0 1 := by
    rw [← h1]
    conv_lhs => rw [← Matrix.fromBlocks_one]
    rw [Matrix.fromBlocks_neg]
    simp [h0]
  rw [hneg]
  simp only [invT, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul, e1, e2]


theorem leviSL_comm_invT (i : K) (A : SL(2, K)) :
    leviSL h (m := m) A * invT i (-i) = invT i (-i) * leviSL h A := by
  simp only [leviSL, invT, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, smul_zero]

section Invol

variable {n : ℕ} {P : Matrix (Fin n) ((Fin 2 ⊕ Fin 2) ⊕ Fin m) K}
  (hP : hadj h P * P = frameGram 2 m K) (hnm : 2 * 2 + m = n)
  {i : K} (hi : h.bar i = i) (hii : i * i = -1)

@[expose] noncomputable def invSU : unitarySU p f K n :=
  frameSU h hP hnm (invT i (-i)) (invT_isometry h hi hii) (det_invT hii)

theorem coe_invSU :
    ((invSU h hP hnm hi hii : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      frameConj h P (invT i (-i)) :=
  rfl

theorem levSU_comm (A : SL(2, K)) :
    levSU h hP hnm A * invSU h hP hnm hi hii = invSU h hP hnm hi hii * levSU h hP hnm A :=
  Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_levSU, coe_invSU,
      frameConj_mul h hP, frameConj_mul h hP, leviSL_comm_invT]))

theorem invSU_sq (hm : m = 0) (hn4 : n = 4) :
    invSU h hP hnm hi hii ^ 2 ∈ unitaryScalars h n := by
  subst hm
  rw [mem_unitaryScalars]
  refine ⟨-1, ?_, ?_, ?_⟩
  · rw [UnitaryFieldData.norm]
    simp
  · rw [hn4, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_one_sq, one_pow]
  · apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, pow_two, coe_invSU, frameConj_mul h hP,
      invT_sq hii, Matrix.GeneralLinearGroup.coe_scalar]
    simp only [frameConj, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, frame_mul_inv h hP hnm,
      Units.val_neg, Units.val_one, map_neg, map_one]

theorem invSU_not_mem (h2 : (2 : K) ≠ 0) :
    invSU h hP hnm hi hii ∉ unitaryScalars h n := by
  intro hmem
  rw [mem_unitaryScalars] at hmem
  obtain ⟨c, -, -, hc⟩ := hmem
  have hT : invT (m := m) i (-i) = (c : K) • 1 := by
    apply eq_smul_of_frameConj_eq_scalar h hP
    rw [← coe_invSU h hP hnm hi hii, hc, Matrix.GeneralLinearGroup.coe_scalar]
  have e1 := congrFun (congrFun hT (Sum.inl (Sum.inl 0))) (Sum.inl (Sum.inl 0))
  have e2 := congrFun (congrFun hT (Sum.inl (Sum.inr 0))) (Sum.inl (Sum.inr 0))
  simp [invT] at e1 e2
  have h2i : (2 : K) * i = 0 := by linear_combination e1 - e2
  rcases mul_eq_zero.mp h2i with h0 | h0
  · exact h2 h0
  · rw [h0, mul_zero] at hii
    exact one_ne_zero (neg_eq_zero.mp hii.symm)

@[expose] noncomputable def invProj : unitaryPSU h n := unitaryProj h n (invSU h hP hnm hi hii)

theorem orderOf_invProj (hm : m = 0) (hn4 : n = 4) (h2 : (2 : K) ≠ 0) :
    orderOf (invProj h hP hnm hi hii) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [invProj, ← map_pow]
    exact MonoidHom.mem_ker.mp (by rw [ker_unitaryProj]; exact invSU_sq h hP hnm hi hii hm hn4)
  · intro h1
    exact invSU_not_mem h hP hnm hi hii h2 (by rw [← ker_unitaryProj]; exact h1)

@[expose] noncomputable def levProj : SL(2, K) →* unitaryPSU h n := (unitaryProj h n).comp (levSU h hP hnm)

theorem levProj_comm (A : SL(2, K)) :
    levProj h hP hnm A * invProj h hP hnm hi hii = invProj h hP hnm hi hii * levProj h hP hnm A := by
  simp only [levProj, invProj, MonoidHom.comp_apply, ← map_mul, levSU_comm h hP hnm hi hii]

theorem sq_eq_one_of_levProj_eq_one (A : SL(2, K)) (hA : levProj h hP hnm A = 1) : A ^ 2 = 1 := by
  have hmem : levSU h hP hnm A ∈ (unitaryProj h n).ker := hA
  rw [ker_unitaryProj, mem_unitaryScalars] at hmem
  obtain ⟨c, -, -, hc⟩ := hmem
  have hT : leviSL h (m := m) A = (c : K) • 1 := by
    apply eq_smul_of_frameConj_eq_scalar h hP
    rw [← coe_levSU h hP hnm, hc, Matrix.GeneralLinearGroup.coe_scalar]
  have hA1 : (A : Matrix (Fin 2) (Fin 2) K) = (c : K) • 1 := by
    ext a b
    have := congrFun (congrFun hT (Sum.inl (Sum.inl a))) (Sum.inl (Sum.inl b))
    simpa [leviSL, Matrix.one_apply] using this
  have hdet : (c : K) * c = 1 := by
    have := A.2
    rw [hA1, Matrix.det_smul, Matrix.det_one] at this
    simpa [pow_two] using this
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_two, hA1, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hdet, one_smul, Matrix.mul_one, Matrix.SpecialLinearGroup.coe_one]

end Invol

end CFSG.RankThree.PartOne.SLBN
