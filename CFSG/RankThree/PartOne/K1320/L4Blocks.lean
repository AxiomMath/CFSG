module

public import CFSG.RankThree.PartOne.K1320.L4Mat
public import CFSG.RankThree.PartOne.KF.R8Levi

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem fidx_symm_zero : fidx.symm (0 : Fin 4) = ⟨0, 0⟩ := rfl
theorem fidx_symm_one : fidx.symm (1 : Fin 4) = ⟨0, 1⟩ := rfl
theorem fidx_symm_two : fidx.symm (2 : Fin 4) = ⟨1, 0⟩ := rfl
theorem fidx_symm_three : fidx.symm (3 : Fin 4) = ⟨1, 1⟩ := rfl

theorem iotaK_apply_qBasis (X : Matrix.SpecialLinearGroup (Fin 2) K) (m n : Fin 2) :
    (qBasis K).repr (iotaK X (qBasis K m)) n = (X : Matrix (Fin 2) (Fin 2) K) n m := by
  have h := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) n m) (glK_iotaK X)
  have h2 : ((glK (iotaK X) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) n m =
      (qBasis K).repr (iotaK X (qBasis K m)) n := by
    show LinearMap.toMatrix (qBasis K) (qBasis K) (iotaK X : Qext K →ₗ[K] Qext K) n m = _
    rw [LinearMap.toMatrix_apply]
    rfl
  rw [← h2]
  exact h

theorem extCoord_single (i j : Fin 2) (g : Qext K ≃ₗ[K] Qext K) (w : Qext K) (k : Fin 2) :
    extCoord i g (Pi.single j w : QV K (Fin 2)) k =
      if k = j then (if j = i then g w else w) else 0 := by
  rw [extCoord_apply]
  by_cases hkj : k = j
  · subst hkj
    by_cases hki : k = i <;> simp [hki]
  · by_cases hki : k = i
    · subst hki
      simp [hkj]
    · simp [hki, hkj]

theorem adSL_blkA_apply (i : Fin 2) (X : Matrix.SpecialLinearGroup (Fin 2) K) (k l : Fin 4) :
    (adSL (blkA i X) : Matrix (Fin 4) (Fin 4) K) k l =
      if (fidx.symm k).1 = (fidx.symm l).1 then
        (if (fidx.symm l).1 = i then (X : Matrix (Fin 2) (Fin 2) K) (fidx.symm k).2 (fidx.symm l).2
         else if (fidx.symm k).2 = (fidx.symm l).2 then 1 else 0)
      else 0 := by
  rw [adSL_apply, fbasis_repr, blkA_apply, fvec, extCoord_single]
  by_cases hkl : (fidx.symm k).1 = (fidx.symm l).1
  · simp only [hkl, ite_true]
    by_cases hli : (fidx.symm l).1 = i
    · simp only [hli, ite_true]
      exact iotaK_apply_qBasis X _ _
    · simp only [hli, ite_false]
      rw [Module.Basis.repr_self, Finsupp.single_apply]
      simp [eq_comm]
  · simp [hkl]

open Matrix.SpecialLinearGroup in
theorem blkA_zero_trU (c : K) :
    blkA 0 (transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c) =
      eM (by decide : (0 : Fin 4) ≠ 1) c := by
  apply adSL.injective
  rw [adSL_eM]
  apply Subtype.ext
  ext k l
  rw [adSL_blkA_apply]
  fin_cases k <;> fin_cases l <;>
    simp [fidx_symm_zero, fidx_symm_one, fidx_symm_two, fidx_symm_three, transvection_coe]

open Matrix.SpecialLinearGroup in
theorem blkA_zero_trL (c : K) :
    blkA 0 (transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c) =
      eM (by decide : (1 : Fin 4) ≠ 0) c := by
  apply adSL.injective
  rw [adSL_eM]
  apply Subtype.ext
  ext k l
  rw [adSL_blkA_apply]
  fin_cases k <;> fin_cases l <;>
    simp [fidx_symm_zero, fidx_symm_one, fidx_symm_two, fidx_symm_three, transvection_coe]

open Matrix.SpecialLinearGroup in
theorem blkA_one_trU (c : K) :
    blkA 1 (transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c) =
      eM (by decide : (2 : Fin 4) ≠ 3) c := by
  apply adSL.injective
  rw [adSL_eM]
  apply Subtype.ext
  ext k l
  rw [adSL_blkA_apply]
  fin_cases k <;> fin_cases l <;>
    simp [fidx_symm_zero, fidx_symm_one, fidx_symm_two, fidx_symm_three, transvection_coe]

open Matrix.SpecialLinearGroup in
theorem blkA_one_trL (c : K) :
    blkA 1 (transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c) =
      eM (by decide : (3 : Fin 4) ≠ 2) c := by
  apply adSL.injective
  rw [adSL_eM]
  apply Subtype.ext
  ext k l
  rw [adSL_blkA_apply]
  fin_cases k <;> fin_cases l <;>
    simp [fidx_symm_zero, fidx_symm_one, fidx_symm_two, fidx_symm_three, transvection_coe]

@[expose] def eGen (K : Type) [Field K] [Finite K] [CharP K 2] (i j : Fin 4) : Set ↥(M8 K) :=
  {g | ∃ (h : i ≠ j) (c : K), g = eM h c ∨ g = eM h.symm c}

@[expose] noncomputable def slB (K : Type) [Field K] [Finite K] [CharP K 2] (i j : Fin 4) :
    Subgroup ↥(M8 K) :=
  Subgroup.closure (eGen K i j)

theorem blkA_zero_range : (blkA (K := K) 0).range = slB K 0 1 := by
  have himg : (blkA (K := K) 0) '' CFSG.LinearGroups.elementarySet 2 K = eGen K 0 1 := by
    ext g
    constructor
    · rintro ⟨A, ⟨i, j, hij, c, rfl⟩, rfl⟩
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact ⟨by decide, c, Or.inl (blkA_zero_trU c)⟩
      · exact ⟨by decide, c, Or.inr (blkA_zero_trL c)⟩
      · exact absurd rfl hij
    · rintro ⟨h, c, rfl | rfl⟩
      · exact ⟨_, ⟨0, 1, zero_ne_one, c, rfl⟩, blkA_zero_trU c⟩
      · exact ⟨_, ⟨1, 0, one_ne_zero, c, rfl⟩, blkA_zero_trL c⟩
  rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 2)
    (K := K), MonoidHom.map_closure, himg]
  rfl

theorem blkA_one_range : (blkA (K := K) 1).range = slB K 2 3 := by
  have himg : (blkA (K := K) 1) '' CFSG.LinearGroups.elementarySet 2 K = eGen K 2 3 := by
    ext g
    constructor
    · rintro ⟨A, ⟨i, j, hij, c, rfl⟩, rfl⟩
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact ⟨by decide, c, Or.inl (blkA_one_trU c)⟩
      · exact ⟨by decide, c, Or.inr (blkA_one_trL c)⟩
      · exact absurd rfl hij
    · rintro ⟨h, c, rfl | rfl⟩
      · exact ⟨_, ⟨0, 1, zero_ne_one, c, rfl⟩, blkA_one_trU c⟩
      · exact ⟨_, ⟨1, 0, one_ne_zero, c, rfl⟩, blkA_one_trL c⟩
  rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 2)
    (K := K), MonoidHom.map_closure, himg]
  rfl

theorem extCoord_zero_comm_one (g h : Qext K ≃ₗ[K] Qext K) :
    extCoord (K := K) 0 g * extCoord 1 h = extCoord 1 h * extCoord 0 g := by
  refine LinearEquiv.ext fun v => funext fun k => ?_
  fin_cases k <;> simp [extCoord_apply]

theorem slB_zero_one_le_centralizer :
    slB K 0 1 ≤ Subgroup.centralizer (slB K 2 3 : Set ↥(M8 K)) := by
  rw [← blkA_zero_range, ← blkA_one_range]
  rintro _ ⟨X, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨Y, rfl⟩
  apply Subtype.ext
  exact (extCoord_zero_comm_one (iotaK X) (iotaK Y)).symm

theorem slB_zero_one_inf_two_three : slB K 0 1 ⊓ slB K 2 3 = ⊥ := by
  rw [← blkA_zero_range, ← blkA_one_range, eq_bot_iff]
  rintro g ⟨⟨X, rfl⟩, ⟨Y, hY⟩⟩
  rw [Subgroup.mem_bot]
  have h1 : iotaK X = iotaK (1 : Matrix.SpecialLinearGroup (Fin 2) K) := by
    refine LinearEquiv.ext fun w => ?_
    have h2 := congrArg (fun m : ↥(M8 K) =>
      (m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (Pi.single 0 w) 0) hY
    simpa [blkA_apply, extCoord_apply] using h2.symm
  have h3 : X = 1 := iotaK_injective h1
  rw [h3, map_one]

@[expose] noncomputable def diagSLmat (a : Kˣ) : Matrix.SpecialLinearGroup (Fin 2) (Qext K) :=
  ⟨!![algebraMap K (Qext K) (a : K), 0; 0, algebraMap K (Qext K) ((a⁻¹ : Kˣ) : K)], by
    rw [Matrix.det_fin_two_of]
    simp⟩

theorem coe_diagSLmat (a : Kˣ) :
    (diagSLmat a : Matrix (Fin 2) (Fin 2) (Qext K)) =
      !![algebraMap K (Qext K) (a : K), 0; 0, algebraMap K (Qext K) ((a⁻¹ : Kˣ) : K)] := rfl

@[expose] noncomputable def diagSL2 : Kˣ →* Matrix.SpecialLinearGroup (Fin 2) (Qext K) where
  toFun := diagSLmat
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_diagSLmat]
  map_mul' a b := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_diagSLmat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem diagSL2_injective : Function.Injective (diagSL2 (K := K)) := by
  intro a b h
  have h1 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) (Qext K) =>
    (X : Matrix (Fin 2) (Fin 2) (Qext K)) 0 0) h
  change (algebraMap K (Qext K)) (a : K) = (algebraMap K (Qext K)) (b : K) at h1
  exact Units.ext ((algebraMap K (Qext K)).injective h1)

@[expose] noncomputable def Tl (K : Type) [Field K] [Finite K] [CharP K 2] : Kˣ →* ↥(M8 K) :=
  (blk8M (K := K)).comp diagSL2

theorem Tl_apply_zero (a : Kˣ) (v : QV K (Fin 2)) :
    ((Tl K a : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v 0 =
      algebraMap K (Qext K) (a : K) * v 0 := by
  show (blk8M (diagSL2 a) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v 0 = _
  simp [blk8M_apply, diagSL2, coe_diagSLmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem Tl_apply_one (a : Kˣ) (v : QV K (Fin 2)) :
    ((Tl K a : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v 1 =
      algebraMap K (Qext K) ((a⁻¹ : Kˣ) : K) * v 1 := by
  show (blk8M (diagSL2 a) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v 1 = _
  simp [blk8M_apply, diagSL2, coe_diagSLmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem Tl_injective : Function.Injective (Tl K) :=
  blk8M_injective.comp diagSL2_injective

theorem Tl_mem_range_blk8M (a : Kˣ) : Tl K a ∈ (blk8M (K := K)).range :=
  ⟨diagSL2 a, rfl⟩

@[expose] noncomputable def tlSL (a : Kˣ) : Matrix.SpecialLinearGroup (Fin 4) K :=
  ⟨Matrix.diagonal ![(a : K), (a : K), ((a⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K)], by
    simp [Matrix.det_diagonal, Fin.prod_univ_four]⟩

omit [Finite K] [CharP K 2] in
theorem coe_tlSL (a : Kˣ) :
    (tlSL a : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal ![(a : K), (a : K), ((a⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K)] := rfl

theorem adSL_Tl (a : Kˣ) : adSL (Tl K a) = tlSL a := by
  apply Subtype.ext
  apply adSL_eq_of_apply
  intro l
  fin_cases l
  · funext i
    fin_cases i <;>
      simp [fvec, fidx_symm_zero, Tl_apply_zero, Tl_apply_one, coe_tlSL, Fin.sum_univ_four,
        Pi.single_apply, Matrix.diagonal_apply, Algebra.smul_def]
  · funext i
    fin_cases i <;>
      simp [fvec, fidx_symm_one, Tl_apply_zero, Tl_apply_one, coe_tlSL, Fin.sum_univ_four,
        Pi.single_apply, Matrix.diagonal_apply, Algebra.smul_def]
  · funext i
    fin_cases i <;>
      simp [fvec, fidx_symm_two, Tl_apply_zero, Tl_apply_one, coe_tlSL, Fin.sum_univ_four,
        Pi.single_apply, Matrix.diagonal_apply, Algebra.smul_def]
  · funext i
    fin_cases i <;>
      simp [fvec, fidx_symm_three, Tl_apply_zero, Tl_apply_one, coe_tlSL, Fin.sum_univ_four,
        Pi.single_apply, Matrix.diagonal_apply, Algebra.smul_def]

@[expose] noncomputable def wSL2 : Matrix.SpecialLinearGroup (Fin 2) (Qext K) :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]⟩

theorem swapM_eq_blk8M : (swapM : ↥(M8 K)) = blk8M wSL2 := by
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  rw [blk8M_apply, coe_swapM, gSwap_apply]
  funext k
  fin_cases k <;> simp [wSL2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem Tl_comm_T8 {p : ℕ} {g : ↥(M8 K)} (hg : g ∈ T8 p K) (a : Kˣ) :
    Tl K a * g = g * Tl K a := by
  obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.1 hg
  apply Subtype.ext
  refine LinearEquiv.ext fun w => funext fun k => ?_
  show ((Tl K a : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
      ((g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) w) k =
    (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
      (((Tl K a : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) w) k
  rw [← hv]
  fin_cases k
  · simp only [Tl_apply_zero, d8Emb_apply_zero, Fin.zero_eta]
    ring
  · simp only [Tl_apply_one, d8Emb_apply_one, Fin.mk_one]
    ring

omit [Finite K] [CharP K 2] in
theorem comm_single_one {X : Matrix (Fin 4) (Fin 4) K} {i j : Fin 4}
    (h : Matrix.single i j (1 : K) * X = X * Matrix.single i j 1) :
    (∀ a, a ≠ i → X a i = 0) ∧ (∀ b, b ≠ j → X j b = 0) ∧ X i i = X j j := by
  refine ⟨fun a ha => ?_, fun b hb => ?_, ?_⟩
  · have := congrFun (congrFun h a) j
    rw [Matrix.single_mul_apply_of_ne (h := ha), Matrix.mul_single_apply_same] at this
    simpa using this.symm
  · have := congrFun (congrFun h i) b
    rw [Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne (hbj := hb)] at this
    simpa using this
  · have := congrFun (congrFun h i) j
    rw [Matrix.single_mul_apply_same, Matrix.mul_single_apply_same] at this
    simpa using this.symm

omit [Finite K] [CharP K 2] in
theorem comm_single_of_comm_transvection {X : Matrix (Fin 4) (Fin 4) K} {i j : Fin 4}
    (h : (1 + Matrix.single i j (1 : K)) * X = X * (1 + Matrix.single i j (1 : K))) :
    Matrix.single i j (1 : K) * X = X * Matrix.single i j 1 := by
  rw [add_mul, mul_add, one_mul, mul_one] at h
  exact add_left_cancel h

omit [Finite K] in
theorem eq_one_of_sq_eq_one {x : K} (h : x ^ 2 = 1) : x = 1 := by
  have h0 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h2 : (x - 1) ^ 2 = 0 := by linear_combination h + (1 - x) * h0
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h2)

omit [Finite K] in
theorem eq_tlSL_of_comm (X : Matrix.SpecialLinearGroup (Fin 4) K)
    (h01 : Matrix.single 0 1 (1 : K) * (X : Matrix (Fin 4) (Fin 4) K) =
      (X : Matrix (Fin 4) (Fin 4) K) * Matrix.single 0 1 1)
    (h10 : Matrix.single 1 0 (1 : K) * (X : Matrix (Fin 4) (Fin 4) K) =
      (X : Matrix (Fin 4) (Fin 4) K) * Matrix.single 1 0 1)
    (h23 : Matrix.single 2 3 (1 : K) * (X : Matrix (Fin 4) (Fin 4) K) =
      (X : Matrix (Fin 4) (Fin 4) K) * Matrix.single 2 3 1)
    (h32 : Matrix.single 3 2 (1 : K) * (X : Matrix (Fin 4) (Fin 4) K) =
      (X : Matrix (Fin 4) (Fin 4) K) * Matrix.single 3 2 1) :
    ∃ a : Kˣ, X = tlSL a := by
  obtain ⟨c01, -, e01⟩ := comm_single_one h01
  obtain ⟨c10, -, -⟩ := comm_single_one h10
  obtain ⟨c23, -, e23⟩ := comm_single_one h23
  obtain ⟨c32, -, -⟩ := comm_single_one h32
  set M : Matrix (Fin 4) (Fin 4) K := (X : Matrix (Fin 4) (Fin 4) K) with hM
  have hdiag : ∀ k l : Fin 4, k ≠ l → M k l = 0 := by
    intro k l hkl
    fin_cases l
    · exact c01 k (by simpa using hkl)
    · exact c10 k (by simpa using hkl)
    · exact c23 k (by simpa using hkl)
    · exact c32 k (by simpa using hkl)
  have hMd : M = Matrix.diagonal fun k => M k k := by
    ext k l
    by_cases hkl : k = l
    · subst hkl
      simp
    · rw [hdiag k l hkl, Matrix.diagonal_apply_ne _ hkl]
  have hdet : M 0 0 * M 1 1 * (M 2 2 * M 3 3) = 1 := by
    have h : M.det = 1 := X.2
    rw [hMd, Matrix.det_diagonal, Fin.prod_univ_four] at h
    simpa [mul_assoc] using h
  rw [← e01, ← e23] at hdet
  have hsq : (M 0 0 * M 2 2) ^ 2 = 1 := by
    rw [← hdet]
    ring
  have h1 : M 0 0 * M 2 2 = 1 := eq_one_of_sq_eq_one hsq
  have hne : M 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hinv : M 2 2 = (M 0 0)⁻¹ := eq_inv_of_mul_eq_one_right h1
  refine ⟨Units.mk0 (M 0 0) hne, ?_⟩
  apply Subtype.ext
  rw [coe_tlSL]
  ext k l
  show M k l = _
  by_cases hkl : k = l
  · subst hkl
    have h11 : M 1 1 = M 0 0 := e01.symm
    have h33 : M 3 3 = M 2 2 := e23.symm
    fin_cases k <;> simp [h11, h33, hinv]
  · rw [hdiag k l hkl, Matrix.diagonal_apply_ne _ hkl]

omit [Finite K] [CharP K 2] in
theorem diagonal_mul_transvection {x : Fin 4 → K} {i j : Fin 4} (hx : x i = x j) (c : K) :
    Matrix.diagonal x * (1 + Matrix.single i j c) =
      (1 + Matrix.single i j c) * Matrix.diagonal x := by
  rw [mul_add, add_mul, mul_one, one_mul]
  congr 1
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hab : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hab
    simp [hx, mul_comm]
  · simp [hab]

theorem Tl_comm_eM (a : Kˣ) {i j : Fin 4} (h : i ≠ j)
    (hx : (![(a : K), (a : K), ((a⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K)] : Fin 4 → K) i =
      (![(a : K), (a : K), ((a⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K)] : Fin 4 → K) j) (c : K) :
    Tl K a * eM h c = eM h c * Tl K a := by
  apply adSL.injective
  rw [map_mul, map_mul, adSL_Tl, adSL_eM]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tlSL,
    Matrix.SpecialLinearGroup.transvection_coe]
  exact diagonal_mul_transvection hx c

theorem centralizer_slB_blocks :
    Subgroup.centralizer ((slB K 0 1 ⊔ slB K 2 3 : Subgroup ↥(M8 K)) : Set ↥(M8 K)) =
      (Tl K).range := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg
    have hc : ∀ {i j : Fin 4} (h : i ≠ j), eM h (1 : K) ∈ slB K 0 1 ⊔ slB K 2 3 →
        Matrix.single i j (1 : K) * (adSL g : Matrix (Fin 4) (Fin 4) K) =
          (adSL g : Matrix (Fin 4) (Fin 4) K) * Matrix.single i j 1 := by
      intro i j h hmem
      have h1 := congrArg (fun y : ↥(M8 K) => (adSL y : Matrix (Fin 4) (Fin 4) K)) (hg _ hmem)
      simp only [map_mul, adSL_eM, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.transvection_coe] at h1
      exact comm_single_of_comm_transvection h1
    have m01 : eM (by decide : (0 : Fin 4) ≠ 1) (1 : K) ∈ slB K 0 1 ⊔ slB K 2 3 :=
      Subgroup.mem_sup_left (Subgroup.subset_closure ⟨by decide, 1, Or.inl rfl⟩)
    have m10 : eM (by decide : (1 : Fin 4) ≠ 0) (1 : K) ∈ slB K 0 1 ⊔ slB K 2 3 :=
      Subgroup.mem_sup_left (Subgroup.subset_closure ⟨by decide, 1, Or.inr rfl⟩)
    have m23 : eM (by decide : (2 : Fin 4) ≠ 3) (1 : K) ∈ slB K 0 1 ⊔ slB K 2 3 :=
      Subgroup.mem_sup_right (Subgroup.subset_closure ⟨by decide, 1, Or.inl rfl⟩)
    have m32 : eM (by decide : (3 : Fin 4) ≠ 2) (1 : K) ∈ slB K 0 1 ⊔ slB K 2 3 :=
      Subgroup.mem_sup_right (Subgroup.subset_closure ⟨by decide, 1, Or.inr rfl⟩)
    obtain ⟨a, ha⟩ := eq_tlSL_of_comm (adSL g) (hc _ m01) (hc _ m10) (hc _ m23) (hc _ m32)
    exact ⟨a, adSL.injective (by rw [adSL_Tl, ha])⟩
  · rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hle : slB K 0 1 ⊔ slB K 2 3 ≤ Subgroup.centralizer ({Tl K a} : Set ↥(M8 K)) := by
      refine sup_le ?_ ?_
      · refine (Subgroup.closure_le _).2 ?_
        rintro g ⟨hij, c, rfl | rfl⟩
        · exact (Subgroup.mem_centralizer_singleton_iff).2
            (Tl_comm_eM a hij (by simp) c).symm
        · exact (Subgroup.mem_centralizer_singleton_iff).2
            (Tl_comm_eM a hij.symm (by simp) c).symm
      · refine (Subgroup.closure_le _).2 ?_
        rintro g ⟨hij, c, rfl | rfl⟩
        · exact (Subgroup.mem_centralizer_singleton_iff).2
            (Tl_comm_eM a hij (by simp) c).symm
        · exact (Subgroup.mem_centralizer_singleton_iff).2
            (Tl_comm_eM a hij.symm (by simp) c).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hh))

end CFSG.RankThree.PartOne.K1320
