module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds

public section

namespace CFSG.StandardType.Triality

open CFSG.LieType.Universal.Spin CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms QuadraticMap

@[expose] def pv2 (k : Fin 4) (b : Bool) : Fin 4 ⊕ Fin 4 → ZMod 2 :=
  Pi.single (if b then Sum.inl k else Sum.inr k) 1

@[expose] def eich2 (i j : Fin 4) (s t : Bool) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  1 + Matrix.vecMulVec (pv2 i s) (pv2 j (!t)) + Matrix.vecMulVec (pv2 j t) (pv2 i (!s))

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def toK8 :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) →* Matrix (Fin (2 * 4)) (Fin (2 * 4)) K :=
  (Matrix.reindexAlgEquiv K K (plusIndexEquiv 4)).toMonoidHom.comp
    (ZMod.castHom (dvd_refl 2) K).mapMatrix.toMonoidHom

theorem toK8_apply (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) (a b : Fin (2 * 4)) :
    toK8 (K := K) A a b =
      ZMod.castHom (dvd_refl 2) K (A ((plusIndexEquiv 4).symm a) ((plusIndexEquiv 4).symm b)) :=
  rfl

theorem toK8_injective : Function.Injective (toK8 (K := K)) := by
  intro A B h
  ext a b
  have h1 := congrFun (congrFun h (plusIndexEquiv 4 a)) (plusIndexEquiv 4 b)
  rw [toK8_apply, toK8_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h1
  exact (ZMod.castHom (dvd_refl 2) K).injective h1


theorem polar_single_plusVec (b : Fin 4 ⊕ Fin 4) (k : Fin 4) (r : Bool) :
    polar (quadPlus 4 K) (Pi.single b 1) (plusVec 4 K k r) =
      ZMod.castHom (dvd_refl 2) K (pv2 k (!r) b) := by
  cases r
  · rw [plusVec_false, polar_quadPlus_single_inr]
    simp only [pv2, Bool.not_false, if_true, Pi.single_apply, eq_comm (a := b)]
    split_ifs <;> simp
  · rw [plusVec_true, polar_quadPlus_single_inl]
    simp only [pv2, Bool.not_true, Bool.false_eq_true, if_false, Pi.single_apply,
      eq_comm (a := b)]
    split_ifs <;> simp

theorem plusVec_apply_eq (k : Fin 4) (r : Bool) (a : Fin 4 ⊕ Fin 4) :
    plusVec 4 K k r a = ZMod.castHom (dvd_refl 2) K (pv2 k r a) := by
  cases r <;> simp only [plusVec_false, plusVec_true, pv2, Bool.false_eq_true, if_false,
    if_true, Pi.single_apply] <;> split_ifs <;> simp

theorem coe_X8_one {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv i j s t) :
    ((X8 γ (1 : K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
      toK8 (eich2 i j s t) := by
  ext a b
  have key := congrFun (X8_mulVec hij h (1 : K) (Pi.single b 1)) a
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at key
  rw [key, toK8_apply]
  set e := plusIndexEquiv 4
  have hb : (Pi.single b (1 : K) : Fin (2 * 4) → K) =
      reindexVectorEquiv e (Pi.single (e.symm b) 1) := by
    rw [AutOm.reindex_single, Equiv.apply_symm_apply]
  have hQ : coordinateQuadPlus 4 K (AutOm.pvec i s) = 0 := by
    change quadPlus 4 K ((reindexVectorEquiv e).symm (reindexVectorEquiv e (plusVec 4 K i s))) = 0
    rw [LinearEquiv.symm_apply_apply, quadPlus_plusVec]
  rw [AutOm.eichlerC, one_smul, hQ, zero_mul, zero_smul, sub_zero, hb, AutOm.pvec, AutOm.pvec,
    AutOm.polar_reindex_plus, AutOm.polar_reindex_plus]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    reindexVectorEquiv_apply, polar_single_plusVec, plusVec_apply_eq]
  rw [CharTwo.sub_eq_add]
  simp only [eich2, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, map_add, map_mul]
  have h1 : (Pi.single (e.symm b) (1 : K) : Fin 4 ⊕ Fin 4 → K) (e.symm a) =
      ZMod.castHom (dvd_refl 2) K (if e.symm a = e.symm b then 1 else 0) := by
    rw [Pi.single_apply]
    split_ifs <;> simp
  rw [h1]
  ring


theorem eq_one_of_coe_eq_one {x : Om8 K}
    (h : ((x : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = 1) : x = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [h]
  rfl

theorem coe_mul_matrix (x y : Om8 K) :
    ((x * y : Om8 K) : GL (Fin (2 * 4)) K).val =
      ((x : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
        ((y : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) :=
  rfl

theorem coe_pow_matrix (x : Om8 K) (n : ℕ) :
    ((x ^ n : Om8 K) : GL (Fin (2 * 4)) K).val =
      ((x : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) ^ n := by
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]

@[expose] def rAP : Fin 4 → ℤ := fromStd (lv 0 1 true true)
@[expose] def rAM : Fin 4 → ℤ := fromStd (lv 0 1 false false)
@[expose] def rBP : Fin 4 → ℤ := fromStd (lv 0 1 true false)
@[expose] def rBM : Fin 4 → ℤ := fromStd (lv 0 1 false true)
@[expose] def rCP : Fin 4 → ℤ := fromStd (lv 2 3 true true)
@[expose] def rCM : Fin 4 → ℤ := fromStd (lv 2 3 false false)

theorem toStdD_rAP : toStdD 4 rAP = lv 0 1 true true := by decide
theorem toStdD_rAM : toStdD 4 rAM = lv 0 1 false false := by decide
theorem toStdD_rBP : toStdD 4 rBP = lv 0 1 true false := by decide
theorem toStdD_rBM : toStdD 4 rBM = lv 0 1 false true := by decide
theorem toStdD_rCP : toStdD 4 rCP = lv 2 3 true true := by decide
theorem toStdD_rCM : toStdD 4 rCM = lv 2 3 false false := by decide

theorem rAP_mem : rAP ∈ rootsD4 := mem_rootsD4_iff.2 ⟨0, 1, by decide, true, true, toStdD_rAP⟩
theorem rAM_mem : rAM ∈ rootsD4 := mem_rootsD4_iff.2 ⟨0, 1, by decide, false, false, toStdD_rAM⟩
theorem rBP_mem : rBP ∈ rootsD4 := mem_rootsD4_iff.2 ⟨0, 1, by decide, true, false, toStdD_rBP⟩
theorem rBM_mem : rBM ∈ rootsD4 := mem_rootsD4_iff.2 ⟨0, 1, by decide, false, true, toStdD_rBM⟩
theorem rCP_mem : rCP ∈ rootsD4 := mem_rootsD4_iff.2 ⟨2, 3, by decide, true, true, toStdD_rCP⟩
theorem rCM_mem : rCM ∈ rootsD4 := mem_rootsD4_iff.2 ⟨2, 3, by decide, false, false, toStdD_rCM⟩

theorem tri_rAM : tri rAM = rBP := by decide
theorem tri_rAP : tri rAP = rBM := by decide
theorem tri_rBM : tri rBM = rCP := by decide
theorem tri_rBP : tri rBP = rCM := by decide
theorem tri_rCP : tri rCP = rAP := by decide
theorem tri_rCM : tri rCM = rAM := by decide
theorem refl0_rBP : refl0 rBP = rAM := by decide
theorem refl0_rBM : refl0 rBM = rAP := by decide

theorem coe_X8_rAP : ((X8 rAP (1 : K) : GL (Fin (2 * 4)) K) : Matrix _ _ K) =
    toK8 (eich2 0 1 true true) := coe_X8_one (by decide) toStdD_rAP
theorem coe_X8_rAM : ((X8 rAM (1 : K) : GL (Fin (2 * 4)) K) : Matrix _ _ K) =
    toK8 (eich2 0 1 false false) := coe_X8_one (by decide) toStdD_rAM
theorem coe_X8_rBP : ((X8 rBP (1 : K) : GL (Fin (2 * 4)) K) : Matrix _ _ K) =
    toK8 (eich2 0 1 true false) := coe_X8_one (by decide) toStdD_rBP
theorem coe_X8_rBM : ((X8 rBM (1 : K) : GL (Fin (2 * 4)) K) : Matrix _ _ K) =
    toK8 (eich2 0 1 false true) := coe_X8_one (by decide) toStdD_rBM
theorem coe_X8_rCP : ((X8 rCP (1 : K) : GL (Fin (2 * 4)) K) : Matrix _ _ K) =
    toK8 (eich2 2 3 true true) := coe_X8_one (by decide) toStdD_rCP
theorem coe_X8_rCM : ((X8 rCM (1 : K) : GL (Fin (2 * 4)) K) : Matrix _ _ K) =
    toK8 (eich2 2 3 false false) := coe_X8_one (by decide) toStdD_rCM


@[expose] def lineW2 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  eich2 0 1 false false * eich2 0 1 true true * eich2 0 1 false true * eich2 0 1 true false

@[expose] def lineW2θ : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  eich2 0 1 true false * eich2 0 1 false true * eich2 2 3 true true * eich2 2 3 false false

@[expose] def lineW2θθ : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  eich2 2 3 false false * eich2 2 3 true true * eich2 0 1 true true * eich2 0 1 false false

theorem lineW2_pow_three : lineW2 ^ 3 = 1 := by decide +kernel
theorem lineW2_ne_one : lineW2 ≠ 1 := by decide +kernel
theorem lineW2_identity : lineW2θθ * lineW2θ * lineW2 = 1 := by decide +kernel
theorem lineW2_sq_identity : lineW2θθ ^ 2 * lineW2θ ^ 2 * lineW2 ^ 2 = 1 := by decide +kernel

theorem eich2_rBP_mul_self : eich2 0 1 true false * eich2 0 1 true false = 1 := by decide +kernel
theorem eich2_rBM_mul_self : eich2 0 1 false true * eich2 0 1 false true = 1 := by decide +kernel

variable [Finite K]

@[expose] noncomputable def lineK : Om8 K := X8 rBP 1 * X8 rBM 1

@[expose] noncomputable def lineW : Om8 K :=
  AutOm.plusRefl (K := K) one_le_four lineK * lineK⁻¹

theorem X8_rBP_mul_self : X8 rBP (1 : K) * X8 rBP 1 = 1 :=
  eq_one_of_coe_eq_one (by
    rw [coe_mul_matrix, coe_X8_rBP, ← map_mul, eich2_rBP_mul_self, map_one])

theorem X8_rBM_mul_self : X8 rBM (1 : K) * X8 rBM 1 = 1 :=
  eq_one_of_coe_eq_one (by
    rw [coe_mul_matrix, coe_X8_rBM, ← map_mul, eich2_rBM_mul_self, map_one])

theorem lineW_eq : lineW (K := K) = X8 rAM 1 * X8 rAP 1 * X8 rBM 1 * X8 rBP 1 := by
  have hBP : (X8 rBP (1 : K))⁻¹ = X8 rBP 1 := inv_eq_of_mul_eq_one_right X8_rBP_mul_self
  have hBM : (X8 rBM (1 : K))⁻¹ = X8 rBM 1 := inv_eq_of_mul_eq_one_right X8_rBM_mul_self
  rw [lineW, lineK, map_mul, plusRefl_X8 rBP_mem, plusRefl_X8 rBM_mem, refl0_rBP, refl0_rBM,
    mul_inv_rev, hBP, hBM]
  group

theorem coe_lineW : ((lineW (K := K) : GL (Fin (2 * 4)) K) : Matrix _ _ K) = toK8 lineW2 := by
  rw [lineW_eq, coe_mul_matrix, coe_mul_matrix, coe_mul_matrix, coe_X8_rAM, coe_X8_rAP,
    coe_X8_rBM, coe_X8_rBP, lineW2, map_mul, map_mul, map_mul]

theorem theta_lineW : theta (lineW (K := K)) = X8 rBP 1 * X8 rBM 1 * X8 rCP 1 * X8 rCM 1 := by
  rw [lineW_eq, map_mul, map_mul, map_mul, theta_X8 rAM_mem, theta_X8 rAP_mem, theta_X8 rBM_mem,
    theta_X8 rBP_mem, tri_rAM, tri_rAP, tri_rBM, tri_rBP]

theorem theta_sq_lineW :
    (theta ^ 2 : MulAut (Om8 K)) lineW = X8 rCM 1 * X8 rCP 1 * X8 rAP 1 * X8 rAM 1 := by
  rw [pow_two, MulAut.mul_apply, theta_lineW, map_mul, map_mul, map_mul, theta_X8 rBP_mem,
    theta_X8 rBM_mem, theta_X8 rCP_mem, theta_X8 rCM_mem, tri_rBP, tri_rBM, tri_rCP, tri_rCM]

theorem coe_theta_lineW :
    ((theta (lineW (K := K)) : GL (Fin (2 * 4)) K) : Matrix _ _ K) = toK8 lineW2θ := by
  rw [theta_lineW, coe_mul_matrix, coe_mul_matrix, coe_mul_matrix, coe_X8_rBP, coe_X8_rBM,
    coe_X8_rCP, coe_X8_rCM, lineW2θ, map_mul, map_mul, map_mul]

theorem coe_theta_sq_lineW :
    (((theta ^ 2 : MulAut (Om8 K)) lineW : GL (Fin (2 * 4)) K) : Matrix _ _ K) =
      toK8 lineW2θθ := by
  rw [theta_sq_lineW, coe_mul_matrix, coe_mul_matrix, coe_mul_matrix, coe_X8_rCM, coe_X8_rCP,
    coe_X8_rAP, coe_X8_rAM, lineW2θθ, map_mul, map_mul, map_mul]

theorem lineW_pow_three : lineW (K := K) ^ 3 = 1 :=
  eq_one_of_coe_eq_one (by rw [coe_pow_matrix, coe_lineW, ← map_pow, lineW2_pow_three, map_one])

theorem lineW_ne_one : lineW (K := K) ≠ 1 := by
  intro h
  have h1 := coe_lineW (K := K)
  rw [h] at h1
  apply lineW2_ne_one
  apply toK8_injective (K := K)
  rw [← h1, map_one]
  rfl

theorem orderOf_lineW : orderOf (lineW (K := K)) = 3 :=
  orderOf_eq_prime lineW_pow_three lineW_ne_one

theorem theta_sq_lineW_mul :
    (theta ^ 2 : MulAut (Om8 K)) lineW * theta lineW * lineW = 1 :=
  eq_one_of_coe_eq_one (by
    rw [coe_mul_matrix, coe_mul_matrix, coe_theta_sq_lineW, coe_theta_lineW, coe_lineW,
      ← map_mul, ← map_mul, lineW2_identity, map_one])

theorem theta_sq_lineW_sq_mul :
    (theta ^ 2 : MulAut (Om8 K)) (lineW ^ 2) * theta (lineW ^ 2) * lineW ^ 2 = 1 :=
  eq_one_of_coe_eq_one (by
    rw [map_pow, map_pow, coe_mul_matrix, coe_mul_matrix, coe_pow_matrix, coe_pow_matrix,
      coe_pow_matrix, coe_theta_sq_lineW, coe_theta_lineW, coe_lineW, ← map_pow, ← map_pow,
      ← map_pow, ← map_mul, ← map_mul, lineW2_sq_identity, map_one])

end CFSG.StandardType.Triality

end
