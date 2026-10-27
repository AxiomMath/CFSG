module

public import CFSG.Milestones.ASVolI.F429.aC7Gen
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Sp4Model

open Matrix CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X7a
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K]

theorem burnsideF429a_Sp_toBlocks₂₁ {g : StatedSp 2 K} (hg : g ∈ Q2 K 1) :
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁ = 0 := by
  ext i j
  have hv : (Pi.single (Sum.inl j) 1 : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 2 := by
    rw [burnsideF4gSpInv_mem_flag_two]
    simp
  have h1 := ((burnsideF4gSpInv_mem_Q2_one g).1 hg _).2 hv
  rw [burnsideF4gSpInv_mem_flag_two] at h1
  simp only [burnsideF4gSpInv_mv, Matrix.mulVec_single_one, Matrix.col_apply] at h1
  fin_cases i
  · exact h1.1
  · exact h1.2

theorem burnsideF429a_blockMat_mulVec_mem_flag_two (A C : Matrix (Fin 2) (Fin 2) K)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ flag 2 K 2) : blockMat A C *ᵥ v ∈ flag 2 K 2 := by
  rw [burnsideF4gSpInv_mem_flag_two] at hv ⊢
  obtain ⟨h0, h1⟩ := hv
  simp [blockMat, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, h0, h1]

theorem burnsideF429a_mem_Q2_one_of_blockMat {g : StatedSp 2 K} {A C : Matrix (Fin 2) (Fin 2) K}
    (hA : IsUnit A.det)
    (hg : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      blockMat A C) : g ∈ Q2 K 1 := by
  have hginv : (((g⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = blockMat A⁻¹ (-(A * C * Aᵀ)) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hg, blockMat_mul_inv hA]
  rw [burnsideF4gSpInv_mem_Q2_one]
  intro v
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := burnsideF429a_blockMat_mulVec_mem_flag_two A⁻¹ (-(A * C * Aᵀ)) h
    rw [← hginv] at this
    have e : burnsideF4gSpInv_mv g⁻¹ (burnsideF4gSpInv_mv g v) = v := by
      rw [← burnsideF4gSpInv_mv_mul, inv_mul_cancel, burnsideF4gSpInv_mv_one]
    rw [← e]
    exact this
  · show ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v ∈ _
    rw [hg]
    exact burnsideF429a_blockMat_mulVec_mem_flag_two A C h

theorem burnsideF429a_blockMat_pow {g : StatedSp 2 K} {A C : Matrix (Fin 2) (Fin 2) K}
    (hA : IsUnit A.det)
    (hg : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      blockMat A C) (n : ℕ) :
    ∃ D : Matrix (Fin 2) (Fin 2) K, (((g ^ n : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = blockMat (A ^ n) D := by
  induction n with
  | zero => exact ⟨0, by simp [blockMat_one]⟩
  | succ n ih =>
    obtain ⟨D, hD⟩ := ih
    refine ⟨C + A⁻¹ * D * A⁻¹ᵀ, ?_⟩
    rw [pow_succ, Subgroup.coe_mul, Units.val_mul, hD, hg, blockMat_mul hA, pow_succ]

theorem burnsideF429a_det_eq_one_of_pow [CharP K 2] {g : StatedSp 2 K}
    {A C : Matrix (Fin 2) (Fin 2) K} (hA : IsUnit A.det)
    (hg : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      blockMat A C) {k : ℕ} (hk : g ^ 2 ^ k = 1) : A.det = 1 := by
  obtain ⟨D, hD⟩ := burnsideF429a_blockMat_pow hA hg (2 ^ k)
  rw [hk] at hD
  have h1 : blockMat (1 : Matrix (Fin 2) (Fin 2) K) 0 = blockMat (A ^ 2 ^ k) D := by
    rw [blockMat_one]
    exact hD
  have h2 := (blockMat_inj (by simp) h1).1
  have h3 : A.det ^ 2 ^ k = 1 := by rw [← Matrix.det_pow, ← h2, Matrix.det_one]
  have h4 : (A.det - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, h3, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by positivity)).mp h4)

theorem burnsideF429a_J_conj [CharP K 2] (B : Matrix (Fin 2) (Fin 2) K) (t : K) :
    B * (Matrix.single (0 : Fin 2) (1 : Fin 2) t + Matrix.single (1 : Fin 2) (0 : Fin 2) t) * Bᵀ =
      Matrix.single (0 : Fin 2) (1 : Fin 2) (B.det * t) +
        Matrix.single (1 : Fin 2) (0 : Fin 2) (B.det * t) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.det_fin_two]
  · linear_combination (B 0 0 * B 0 1 * t) * h2
  · linear_combination (B 0 1 * B 1 0 * t) * h2
  · linear_combination (B 0 1 * B 1 0 * t) * h2
  · linear_combination (B 1 0 * B 1 1 * t) * h2

theorem burnsideF429a_blockMat_comm_iff {A C B D : Matrix (Fin 2) (Fin 2) K} (hA : IsUnit A.det)
    (hB : IsUnit B.det) :
    blockMat A C * blockMat B D = blockMat B D * blockMat A C ↔
      A * B = B * A ∧ D + B⁻¹ * C * B⁻¹ᵀ = C + A⁻¹ * D * A⁻¹ᵀ := by
  rw [blockMat_mul hB, blockMat_mul hA]
  constructor
  · intro h
    exact blockMat_inj (by rw [Matrix.det_mul]; exact hA.mul hB) h
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

theorem burnsideF429a_xs_blockMat (t : K) :
    (((burnsideF4gSpInv_xs t : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      blockMat 1 (Matrix.single (0 : Fin 2) (1 : Fin 2) t +
        Matrix.single (1 : Fin 2) (0 : Fin 2) t) := by
  rw [burnsideF4gSpInv_xs_val]
  simp [blockMat]

theorem burnsideF429a_comm_xs_of_pow [CharP K 2] {x : StatedSp 2 K} (hx : x ∈ Q2 K 1) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) (t : K) :
    x * burnsideF4gSpInv_xs t = burnsideF4gSpInv_xs t * x := by
  obtain ⟨hdet, C, -, hxC⟩ :=
    exists_blockMat_of_toBlocks₂₁_eq_zero (burnsideF429a_Sp_toBlocks₂₁ hx)
  have hA1 := burnsideF429a_det_eq_one_of_pow hdet hxC hk
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hxC,
    burnsideF429a_xs_blockMat, burnsideF429a_blockMat_comm_iff hdet (by simp)]
  refine ⟨by simp, ?_⟩
  rw [inv_one, transpose_one, Matrix.one_mul, Matrix.mul_one, burnsideF429a_J_conj,
    Matrix.det_nonsing_inv, hA1, Ring.inverse_one, one_mul]
  abel

theorem burnsideF429a_Xs_le_ctr [CharP K 2] :
    burnsideF4gSpInv_Xs K ≤ ctr (oPPrime 2 (Q2 K 1)) := by
  intro g hg
  obtain ⟨t, rfl⟩ := burnsideF4gSpInv_mem_Xs.1 hg
  have hxsQ : burnsideF4gSpInv_xs t ∈ Q2 K 1 :=
    burnsideF429a_mem_Q2_one_of_blockMat (by simp) (burnsideF429a_xs_blockMat t)
  have hle : oPPrime 2 (Q2 K 1) ≤
      Subgroup.centralizer ({burnsideF4gSpInv_xs t} : Set (StatedSp 2 K)) := by
    unfold oPPrime
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxQ, k, hk⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact burnsideF429a_comm_xs_of_pow hxQ (k := k) (by rw [← hk]; exact pow_orderOf_eq_one x) t
  refine Subgroup.mem_inf.2 ⟨burnsideF4gU4Inv_mem_oPPrime hxsQ (k := 1)
    (by rw [pow_one, pow_two]; exact burnsideF4gSpInv_xs_sq t), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

theorem burnsideF429a_isUnitriangular_N :
    IsUnitriangular (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i <;> rfl

theorem burnsideF429a_unipotent_le_oPPrime_one [Finite K] [CharP K 2] :
    unipotent 2 K ≤ oPPrime 2 (Q2 K 1) := by
  intro u hu
  have huQ : u ∈ Q2 K 1 := by
    have := unipotent_le_borelSubgroup hu
    rw [← burnsideF4gSpInv_Q2_inf_eq_borel] at this
    exact this.2
  refine Subgroup.subset_closure ⟨huQ, ?_⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 burnsideF4gSpInv_unipotent_isPGroup ⟨u, hu⟩
  exact ⟨k, by rw [← hk]; exact Subgroup.orderOf_coe (⟨u, hu⟩ : unipotent 2 K)⟩

theorem burnsideF429a_eq_one_of_sq [CharP K 2] {a : K} (h : a * a = 1) : a = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (a - 1) ^ 2 = 0 := by linear_combination h + (1 - a) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)

theorem burnsideF429a_ctr_L2_le [Finite K] [CharP K 2] :
    ctr (oPPrime 2 (Q2 K 1)) ≤ burnsideF4gSpInv_Xs K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rintro z ⟨hzO, hzC⟩
  have hzQ : z ∈ Q2 K 1 := burnsideF4gG2Inv_oPPrime_le _ hzO
  have hc := Subgroup.mem_centralizer_iff.1 hzC
  obtain ⟨hdet, C, hC, hzM⟩ :=
    exists_blockMat_of_toBlocks₂₁_eq_zero (burnsideF429a_Sp_toBlocks₂₁ hzQ)
  set A := ((z : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁
    with hAdef
  have hS : ∀ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S → A⁻¹ * S * A⁻¹ᵀ = S := by
    intro S hSs
    obtain ⟨u, hu, huM⟩ := exists_mem_unipotent (r := 2) (K := K) isUnitriangular_one hSs
    have e := congrArg (fun g : StatedSp 2 K =>
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
      (hc u (burnsideF429a_unipotent_le_oPPrime_one hu))
    simp only [Subgroup.coe_mul, Units.val_mul, huM, hzM] at e
    have e2 := ((burnsideF429a_blockMat_comm_iff hdet (by simp)).1 e.symm).2
    simp only [inv_one, transpose_one, Matrix.one_mul, Matrix.mul_one] at e2
    rw [add_comm S C] at e2
    exact (add_left_cancel e2).symm
  have hE0 := hS (Matrix.single 0 0 1) (by ext i j; fin_cases i <;> fin_cases j <;> simp)
  have hE1 := hS (Matrix.single 1 1 1) (by ext i j; fin_cases i <;> fin_cases j <;> simp)
  have e00 := congrFun (congrFun hE0 0) 0
  have e10 := congrFun (congrFun hE0 1) 1
  have e01 := congrFun (congrFun hE1 0) 0
  have e11 := congrFun (congrFun hE1 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply] at e00 e10 e01 e11
  have hB : A⁻¹ = 1 := by
    have a00 := burnsideF429a_eq_one_of_sq e00
    have a11 := burnsideF429a_eq_one_of_sq e11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a00, a11, e10, e01]
  have hA : A = 1 := by
    rw [← Matrix.nonsing_inv_nonsing_inv A hdet, hB, inv_one]
  rw [hA] at hzM
  obtain ⟨a, hNa, hNi⟩ :=
    burnsideF4gSpInv_unitriangular_two (burnsideF429a_isUnitriangular_N (K := K))
  have ha1 : a = 1 := by
    have h := congrFun (congrFun hNa 0) 1
    simpa using h.symm
  obtain ⟨u, hu, huM⟩ := exists_mem_unipotent (r := 2) (K := K) (A := !![1, 1; 0, 1]) (C := 0)
    burnsideF429a_isUnitriangular_N transpose_zero
  have eN := congrArg (fun g : StatedSp 2 K =>
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (hc u (burnsideF429a_unipotent_le_oPPrime_one hu))
  simp only [Subgroup.coe_mul, Units.val_mul, huM, hzM] at eN
  have eN2 := ((burnsideF429a_blockMat_comm_iff (by simp)
    (burnsideF429a_isUnitriangular_N (K := K)).isUnit_det).1 eN.symm).2
  rw [hNi, ha1] at eN2
  have c10 : C 1 0 = C 0 1 := by
    have := congrFun (congrFun hC 0) 1
    simpa using this
  have c11 : C 1 1 = 0 := by
    have := congrFun (congrFun eN2 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      Matrix.transpose_apply] at this
    linear_combination this + c10 + C 0 1 * h2
  have hL : IsUnit (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K).det := by
    simp [Matrix.det_fin_two_of]
  obtain ⟨w, hwM⟩ := blockMat_mem_statedSp hL (C := (0 : Matrix (Fin 2) (Fin 2) K)) transpose_zero
  have hwQ : w ∈ Q2 K 1 := burnsideF429a_mem_Q2_one_of_blockMat hL hwM
  have hLL : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, 0; 1, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]
  have hLi : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K)⁻¹ = !![1, 0; 1, 1] :=
    Matrix.inv_eq_right_inv hLL
  have hww : w * w = 1 := by
    apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    rw [Subgroup.coe_mul, Units.val_mul, hwM, blockMat_mul hL, hLL]
    simp [blockMat_one]
  have hwO : w ∈ oPPrime 2 (Q2 K 1) :=
    burnsideF4gU4Inv_mem_oPPrime hwQ (k := 1) (by rw [pow_one, pow_two]; exact hww)
  have eL := congrArg (fun g : StatedSp 2 K =>
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (hc w hwO)
  simp only [Subgroup.coe_mul, Units.val_mul, hwM, hzM] at eL
  have eL2 := ((burnsideF429a_blockMat_comm_iff (by simp) hL).1 eL.symm).2
  rw [hLi] at eL2
  have c00 : C 0 0 = 0 := by
    have := congrFun (congrFun eL2 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      Matrix.transpose_apply] at this
    exact this
  refine burnsideF4gSpInv_mem_Xs.2 ⟨C 0 1, ?_⟩
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [burnsideF429a_xs_blockMat, hzM]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c00, c11, c10]

theorem burnsideF429a_Sp_ctr_L2 [Finite K] [CharP K 2] :
    ctr (oPPrime 2 (Q2 K 1)) = burnsideF4gSpInv_Xs K :=
  le_antisymm burnsideF429a_ctr_L2_le burnsideF429a_Xs_le_ctr

theorem burnsideF429a_Sp_ctr_L1 [Finite K] [CharP K 2] :
    ctr (oPPrime 2 (Q2 K 0)) = burnsideF4gSpInv_Xl K := by
  apply le_antisymm
  · intro z hz
    obtain ⟨t, rfl⟩ := burnsideF4gSpInv_ctr_oPPrime hz
    exact burnsideF4gSpInv_mem_Xl.2 ⟨t, rfl⟩
  · intro g hg
    obtain ⟨t, rfl⟩ := burnsideF4gSpInv_mem_Xl.1 hg
    rw [burnsideF4gSpInv_oPPrime_eq_S1]
    by_cases ht : t = 0
    · rw [ht, burnsideF4gSpInv_xl_zero]
      exact one_mem _
    · have hC := burnsideF4gSpInv_centralizer_xl ht
      have hmem : burnsideF4gSpInv_xl t ∈ burnsideF4gSpInv_S1 K := by
        rw [← hC]
        exact Subgroup.mem_centralizer_singleton_iff.2 rfl
      refine Subgroup.mem_inf.2 ⟨hmem, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      rw [← hC] at hx
      exact Subgroup.mem_centralizer_singleton_iff.1 hx

theorem burnsideF429a_ctr_unipotent [CharP K 2] {y : StatedSp 2 K}
    (hy : y ∈ ctr (unipotent 2 K)) :
    ∃ s t : K, y = burnsideF4gSpInv_xl s * burnsideF4gSpInv_xs t := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hyU, hyC⟩ := hy
  obtain ⟨A, C, hA, hC, hyM⟩ := mem_unipotent.1 hyU
  have hc := Subgroup.mem_centralizer_iff.1 hyC
  obtain ⟨a, hAa, hAi⟩ := burnsideF4gSpInv_unitriangular_two hA
  obtain ⟨u1, hu1, hu1M⟩ := exists_mem_unipotent (r := 2) (K := K) (A := 1)
    (C := Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : K)) isUnitriangular_one (by simp)
  have e1 := congrArg (fun g : StatedSp 2 K =>
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (hc u1 hu1)
  simp only [Subgroup.coe_mul, Units.val_mul, hyM, hu1M] at e1
  rw [blockMat, blockMat, fromBlocks_multiply, fromBlocks_multiply] at e1
  have e1b := (fromBlocks_inj.1 e1).2.1
  have ha : a = 0 := by
    have h := congrFun (congrFun e1b 0) 1
    rw [hAi, hAa] at h
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.vecMul,
      dotProduct] at h
    linear_combination h
  rw [ha] at hAa
  have hA1 : A = 1 := by
    rw [hAa]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  subst hA1
  obtain ⟨b, hNb, hNi⟩ := burnsideF4gSpInv_unitriangular_two
    (burnsideF429a_isUnitriangular_N (K := K))
  obtain ⟨u2, hu2, hu2M⟩ := exists_mem_unipotent (r := 2) (K := K)
    (A := !![1, 1; 0, 1]) (C := 0) burnsideF429a_isUnitriangular_N transpose_zero
  have e2 := congrArg (fun g : StatedSp 2 K =>
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (hc u2 hu2)
  simp only [Subgroup.coe_mul, Units.val_mul, hyM, hu2M] at e2
  rw [blockMat, blockMat, fromBlocks_multiply, fromBlocks_multiply] at e2
  have e2b := (fromBlocks_inj.1 e2).2.1
  have hb1 : b = 1 := by
    have h := congrFun (congrFun hNb 0) 1
    simpa using h.symm
  have hC11 : C 1 1 = 0 := by
    have h := congrFun (congrFun e2b 0) 1
    rw [hNi, hb1] at h
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at h
    linear_combination h
  have hC10 : C 1 0 = C 0 1 := by
    have := congrFun (congrFun hC 0) 1
    simpa using this
  refine ⟨C 0 0, C 0 1, Subtype.ext (Units.ext ?_)⟩
  rw [hyM, Subgroup.coe_mul, Units.val_mul, burnsideF4gSpInv_xl_val, burnsideF4gSpInv_xs_val,
    blockMat, fromBlocks_multiply]
  simp only [inv_one, transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, hC10, hC11]

theorem burnsideF429a_Sp_ctr_U [CharP K 2] :
    ctr (unipotent 2 K) = burnsideF4gSpInv_Xl K ⊔ burnsideF4gSpInv_Xs K := by
  apply le_antisymm
  · intro y hy
    obtain ⟨s, t, rfl⟩ := burnsideF429a_ctr_unipotent hy
    exact Subgroup.mul_mem_sup (burnsideF4gSpInv_mem_Xl.2 ⟨s, rfl⟩)
      (burnsideF4gSpInv_mem_Xs.2 ⟨t, rfl⟩)
  · refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨t, rfl⟩ := burnsideF4gSpInv_mem_Xl.1 hg
      exact burnsideF4gSpInv_xl_mem_ctr t
    · obtain ⟨t, rfl⟩ := burnsideF4gSpInv_mem_Xs.1 hg
      exact burnsideF4gSpInv_xs_mem_ctr t

theorem burnsideF429a_Sp_Xl_inf_Xs : burnsideF4gSpInv_Xl K ⊓ burnsideF4gSpInv_Xs K = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hl, hs⟩
  obtain ⟨s, rfl⟩ := burnsideF4gSpInv_mem_Xl.1 hl
  obtain ⟨t, ht⟩ := burnsideF4gSpInv_mem_Xs.1 hs
  have e := congrArg (fun g : StatedSp 2 K =>
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Sum.inl 0) (Sum.inr 0)) ht
  simp [burnsideF4gSpInv_xl_val, burnsideF4gSpInv_xs_val, Matrix.single_apply] at e
  rw [Subgroup.mem_bot, ← e, burnsideF4gSpInv_xl_zero]

end Sp4Model

section Sp4Final

open Matrix CFSG.ASVolI.ChF.ClassicalRoots CFSG.QuasithinUnique.Setup.X7a
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

theorem burnsideF429a_c7_Sp4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) :
    ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) =
        ctr (oPPrime 2 (Gp ⊓ M₁)) ⊔ ctr (oPPrime 2 (Gp ⊓ M₂)) ∧
      ctr (oPPrime 2 (Gp ⊓ M₁)) ⊓ ctr (oPPrime 2 (Gp ⊓ M₂)) = ⊥ ∧
      ctr (oPPrime 2 (Gp ⊓ M₁)) = hyp.toHypF_4_4g.chart.longRoot ∧
      ctr (oPPrime 2 (Gp ⊓ M₂)) = hyp.toHypF_4_4g.chart.shortRoot := by
  have hM := hyp.toHypF_4_4g.chart_matches
  obtain ⟨marking, hpts, hlines, hlong, hshort⟩ :=
    burnsideF4gSpInv_marking_of_chart hyp.toHypF_4_4g.chart
  have hK : Nat.card marking.field = 2 ^ f := by simpa using marking.field_card
  haveI : CharP marking.field 2 := burnsideF4gSp_charP_of_card hK
  have hbasis : marking.basis = 1 := marking.basis_compatible
  have hinj : Function.Injective (marking.transport : StatedSp 2 marking.field →* ↥Gp) := by
    refine (injective_iff_map_eq_one _).2 fun a ha => ?_
    have h2 := (burnsideF4f_transport_eq_one_iff marking a).1 ha
    exact Subtype.ext (burnsideF4gSpInv_scalar_eq_one h2 a.2)
  let Ψ : StatedSp 2 marking.field ≃* ↥Gp :=
    MulEquiv.ofBijective marking.transport ⟨hinj, burnsideF4f_transport_surjective marking⟩
  have hΨ : Ψ.toMonoidHom = (marking.transport : StatedSp 2 marking.field →* ↥Gp) :=
    MonoidHom.ext fun _ => rfl
  have keyS : ∀ (S : Set (Fin 2 ⊕ Fin 2))
      (W : Submodule marking.field (Fin 2 ⊕ Fin 2 → marking.field))
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) marking.field),
      (∀ v, v ∈ coordinateSpace S ↔ v ∈ W) →
      ((∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ coordinateSpace S ↔
          v ∈ coordinateSpace S) ↔
        ∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ W ↔ v ∈ W) := by
    intro S W A hS
    simp only [hS]
  have key : ∀ b : Bool, nativeParabolic .Sp4 (2 ^ f) marking.field marking.basis b =
      Q2 marking.field (if b then 1 else 0) := by
    intro b
    rw [hbasis]
    ext g
    have h1 : g ∈ nativeParabolic .Sp4 (2 ^ f) marking.field 1 b ↔
        (g : GL (Coord .Sp4) marking.field) ∈ rawStabilizer ((fun vector =>
            ((1 : GL (Coord .Sp4) marking.field) : Matrix (Coord .Sp4) (Coord .Sp4)
              marking.field).mulVec vector) ''
          coordinateSpace (if b then flagTwo .Sp4 else flagOne .Sp4 : Set (Coord .Sp4))) :=
      Iff.rfl
    rw [h1, burnsideF4gSp_mem_rawStabilizer, burnsideF4gSp_image_one, Q2]
    refine Iff.trans ?_
      (burnsideF4gSp_mem_stabilizer_iff (r := 2) (K := marking.field) _ g).symm
    cases b
    · exact keyS _ _ _ (fun v => (burnsideF4gSp_coordinateSpace_flag v).1)
    · exact keyS _ _ _ (fun v => (burnsideF4gSp_coordinateSpace_flag v).2)
  have hpar : ∀ b : Bool, marking.parabolic b =
      (Q2 marking.field (if b then 1 else 0)).map Ψ.toMonoidHom := by
    intro b
    rw [hΨ]
    exact congrArg (Subgroup.map marking.transport) (key b)
  have hM₁ : M₁.subgroupOf Gp = (Q2 marking.field 0).map Ψ.toMonoidHom := by
    have h : Gp ⊓ M₁ = (marking.parabolic false).map Gp.subtype := hM.2.1.trans hpts
    have h2 : M₁.subgroupOf Gp = marking.parabolic false := by
      rw [← Subgroup.inf_subgroupOf_left M₁ Gp, h]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    rw [h2]
    simpa using hpar false
  have hM₂ : M₂.subgroupOf Gp = (Q2 marking.field 1).map Ψ.toMonoidHom := by
    have h : Gp ⊓ M₂ = (marking.parabolic true).map Gp.subtype := hM.2.2.trans hlines
    have h2 : M₂.subgroupOf Gp = marking.parabolic true := by
      rw [← Subgroup.inf_subgroupOf_left M₂ Gp, h]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    rw [h2]
    simpa using hpar true
  have hXl : nativeRoot .Sp4 (2 ^ f) marking.basis .longOne false =
      burnsideF4gSpInv_Xl marking.field := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨-, t, c, -, hg⟩
      refine (burnsideF4gSpInv_mem_Xl (K := marking.field) (g := g)).2 ⟨t, ?_⟩
      apply statedSp_ext
      rw [← burnsideF4gSpInv_matrixUnit_long, hg, hbasis]
      simp [markedMatrix, positiveMatrix, symplecticRoot]
    · intro g hg
      obtain ⟨t, ht⟩ := (burnsideF4gSpInv_mem_Xl (K := marking.field) (g := g)).1 hg
      subst ht
      refine Subgroup.subset_closure ⟨Or.inr (Or.inr (Or.inl rfl)), t, 0, trivial, ?_⟩
      rw [hbasis, ← burnsideF4gSpInv_matrixUnit_long]
      simp [markedMatrix, positiveMatrix, symplecticRoot]
  have hXs : nativeRoot .Sp4 (2 ^ f) marking.basis .sum false =
      burnsideF4gSpInv_Xs marking.field := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨-, t, c, -, hg⟩
      refine (burnsideF4gSpInv_mem_Xs (K := marking.field) (g := g)).2 ⟨t, ?_⟩
      apply statedSp_ext
      rw [← burnsideF4gSpInv_matrixUnit_short, hg, hbasis]
      simp [markedMatrix, positiveMatrix, symplecticRoot]
    · intro g hg
      obtain ⟨t, ht⟩ := (burnsideF4gSpInv_mem_Xs (K := marking.field) (g := g)).1 hg
      subst ht
      refine Subgroup.subset_closure ⟨Or.inr (Or.inl rfl), t, 0, trivial, ?_⟩
      rw [hbasis, ← burnsideF4gSpInv_matrixUnit_short]
      simp [markedMatrix, positiveMatrix, symplecticRoot]
  have hl : hyp.toHypF_4_4g.chart.longRoot =
      (burnsideF4gSpInv_Xl marking.field).map (Gp.subtype.comp Ψ.toMonoidHom) := by
    rw [hlong]
    unfold Marking.root
    rw [hXl]
    exact Subgroup.map_map _ _ _
  have hs : hyp.toHypF_4_4g.chart.shortRoot =
      (burnsideF4gSpInv_Xs marking.field).map (Gp.subtype.comp Ψ.toMonoidHom) := by
    rw [hshort]
    unfold Marking.root
    rw [hXs]
    exact Subgroup.map_map _ _ _
  have hφ : Function.Injective (Gp.subtype.comp Ψ.toMonoidHom) :=
    Gp.subtype_injective.comp Ψ.injective
  obtain ⟨k1, k2, k3⟩ := burnsideF429a_model_ctr Ψ hM₁ hM₂
  rw [k1, k2, k3, hl, hs, burnsideF4gSpInv_Q2_inf_eq_borel, burnsideF4gSpInv_pCoreOf_borel,
    burnsideF429a_Sp_ctr_U, burnsideF429a_Sp_ctr_L1, burnsideF429a_Sp_ctr_L2]
  refine ⟨Subgroup.map_sup _ _ _, ?_, rfl, rfl⟩
  rw [← Subgroup.map_inf_eq _ _ _ hφ, burnsideF429a_Sp_Xl_inf_Xs, Subgroup.map_bot]

end Sp4Final

end CFSG.ASVolI
