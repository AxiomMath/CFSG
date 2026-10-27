module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat

public section

namespace CFSG.RankThree.PartTwo.Late.KFParSp6

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

@[expose] abbrev J6 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem pairedSympForm_eq_dot (x y : Fin 3 ⊕ Fin 3 → ZMod 2) :
    pairedSympForm (ZMod 2) 3 x y = x ⬝ᵥ (J6 *ᵥ y) := by
  rw [pairedSympForm, Matrix.toBilin'_apply']
  rfl

theorem J6_mulVec_inl (x : Fin 3 ⊕ Fin 3 → ZMod 2) (i : Fin 3) :
    (J6 *ᵥ x) (Sum.inl i) = x (Sum.inr i) := by
  simp [J6, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

theorem neg_eq_self_zmod2 (a : ZMod 2) : -a = a := by
  fin_cases a <;> rfl

theorem J6_mulVec_inr (x : Fin 3 ⊕ Fin 3 → ZMod 2) (i : Fin 3) :
    (J6 *ᵥ x) (Sum.inr i) = -x (Sum.inl i) := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have h1 : ∀ a : Fin 3, J6 (Sum.inr i) (Sum.inl a) * x (Sum.inl a) =
      (if i = a then x (Sum.inl a) else 0) := by
    intro a
    by_cases hia : i = a
    · simp [J6, Matrix.one_apply, hia, neg_eq_self_zmod2]
    · simp [J6, Matrix.one_apply, hia, neg_eq_self_zmod2]
  have h2 : ∀ a : Fin 3, J6 (Sum.inr i) (Sum.inr a) * x (Sum.inr a) = 0 := by
    intro a
    simp [J6]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_congr rfl (fun a _ => h2 a),
    Finset.sum_const_zero, add_zero, neg_eq_self_zmod2]
  simp [Finset.sum_ite_eq]

theorem J6_transpose : J6ᵀ = J6 := by
  have hneg : (-1 : ZMod 2) = 1 := by decide
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [J6, Matrix.fromBlocks, hneg, Matrix.one_apply, eq_comm] <;>
    (try split_ifs) <;> decide

theorem pairedSympForm_comm (x y : Fin 3 ⊕ Fin 3 → ZMod 2) :
    pairedSympForm (ZMod 2) 3 x y = pairedSympForm (ZMod 2) 3 y x := by
  rw [pairedSympForm_eq_dot, pairedSympForm_eq_dot, dotProduct_mulVec, ← mulVec_transpose,
    J6_transpose, dotProduct_comm]

theorem pairedSympForm_self (x : Fin 3 ⊕ Fin 3 → ZMod 2) :
    pairedSympForm (ZMod 2) 3 x x = 0 := by
  rw [pairedSympForm_eq_dot, dotProduct, Fintype.sum_sum_type]
  simp only [J6_mulVec_inl, J6_mulVec_inr, neg_eq_self_zmod2]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k _
  rw [mul_comm, CharTwo.add_self_eq_zero]

theorem vecMulVec_mulVec_apply (v w x : Fin 3 ⊕ Fin 3 → ZMod 2) :
    Matrix.vecMulVec v w *ᵥ x = (w ⬝ᵥ x) • v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

@[expose] def tvMat (v : Fin 3 ⊕ Fin 3 → ZMod 2) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  1 + Matrix.vecMulVec v (J6 *ᵥ v)

theorem tvMat_mulVec (v x : Fin 3 ⊕ Fin 3 → ZMod 2) :
    tvMat v *ᵥ x = x + pairedSympForm (ZMod 2) 3 x v • v := by
  rw [pairedSympForm_eq_dot, tvMat, Matrix.add_mulVec, Matrix.one_mulVec,
    vecMulVec_mulVec_apply, dotProduct_comm]

theorem add_self_zero_mat (N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    N + N = 0 := by
  ext i j
  simp [CharTwo.add_self_eq_zero]

theorem one_add_mul_self_mat (N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    (1 + N) * (1 + N) = 1 + (N + N) + N * N := by
  noncomm_ring

theorem tvMat_mul_self (v : Fin 3 ⊕ Fin 3 → ZMod 2) : tvMat v * tvMat v = 1 := by
  have hdot : (J6 *ᵥ v) ⬝ᵥ v = 0 := by
    rw [dotProduct_comm, ← pairedSympForm_eq_dot, pairedSympForm_self]
  have hN : Matrix.vecMulVec v (J6 *ᵥ v) * Matrix.vecMulVec v (J6 *ᵥ v) = 0 := by
    simp [Matrix.vecMulVec_mul_vecMulVec, hdot]
  rw [tvMat, one_add_mul_self_mat, add_self_zero_mat, hN]
  simp

theorem tvMat_form (v x y : Fin 3 ⊕ Fin 3 → ZMod 2) :
    pairedSympForm (ZMod 2) 3 (tvMat v *ᵥ x) (tvMat v *ᵥ y) =
      pairedSympForm (ZMod 2) 3 x y := by
  rw [tvMat_mulVec, tvMat_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    pairedSympForm_self, mul_zero, zero_add, add_zero]
  rw [pairedSympForm_comm v y]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (pairedSympForm (ZMod 2) 3 x v * pairedSympForm (ZMod 2) 3 y v) * h2

theorem gram_of_form (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))
    (h : ∀ x y, pairedSympForm (ZMod 2) 3 (A *ᵥ x) (A *ᵥ y) = pairedSympForm (ZMod 2) 3 x y) :
    Aᵀ * J6 * A = J6 := by
  have hx : ∀ x y : Fin 3 ⊕ Fin 3 → ZMod 2,
      x ⬝ᵥ ((Aᵀ * J6 * A) *ᵥ y) = (A *ᵥ x) ⬝ᵥ (J6 *ᵥ (A *ᵥ y)) := by
    intro x y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  have hq : ∀ x y : Fin 3 ⊕ Fin 3 → ZMod 2,
      x ⬝ᵥ ((Aᵀ * J6 * A) *ᵥ y) = x ⬝ᵥ (J6 *ᵥ y) := by
    intro x y
    rw [hx]
    have := h x y
    rw [pairedSympForm_eq_dot, pairedSympForm_eq_dot] at this
    exact this
  ext i j
  have := hq (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single_one, dotProduct_single, single_dotProduct] using this

@[expose] def tvUnit (v : Fin 3 ⊕ Fin 3 → ZMod 2) :
    Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Units.mk (tvMat v) (tvMat v) (tvMat_mul_self v) (tvMat_mul_self v)

theorem tvUnit_mem (v : Fin 3 ⊕ Fin 3 → ZMod 2) : tvUnit v ∈ StatedSp 3 (ZMod 2) := by
  show tvUnit v ∈ Subgroup.closure _
  apply Subgroup.subset_closure
  exact gram_of_form (tvMat v) (tvMat_form v)

theorem exists_J_coord (v : Fin 3 ⊕ Fin 3 → ZMod 2) (hv : v ≠ 0) :
    ∃ s : Fin 3 ⊕ Fin 3, (J6 *ᵥ v) s = 1 := by
  have hJv : J6 *ᵥ v ≠ 0 := by
    intro h
    apply hv
    funext s
    rcases s with i | i
    · have := congrFun h (Sum.inr i)
      rw [J6_mulVec_inr] at this
      have h1 : -v (Sum.inl i) = 0 := by simpa using this
      exact neg_eq_zero.mp h1
    · have := congrFun h (Sum.inl i)
      rw [J6_mulVec_inl] at this
      simpa using this
  obtain ⟨s, hs⟩ := Function.ne_iff.mp hJv
  refine ⟨s, ?_⟩
  have h01 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  exact h01 _ hs

theorem tvUnit_val (v : Fin 3 ⊕ Fin 3 → ZMod 2) :
    ((tvUnit v : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) = tvMat v :=
  rfl

theorem central_comm_matrix {z : StatedSp 3 (ZMod 2)}
    (hz : z ∈ Subgroup.center (StatedSp 3 (ZMod 2))) (v : Fin 3 ⊕ Fin 3 → ZMod 2) :
    tvMat v * ((z : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) =
    ((z : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) * tvMat v := by
  have h2 : tvUnit v * (z : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) =
      (z : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) * tvUnit v :=
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨tvUnit v, tvUnit_mem v⟩)
  have h3 := congrArg Units.val h2
  rw [Units.val_mul, Units.val_mul, tvUnit_val] at h3
  exact h3

theorem central_comm_mulVec {z : StatedSp 3 (ZMod 2)}
    (hz : z ∈ Subgroup.center (StatedSp 3 (ZMod 2))) (v x : Fin 3 ⊕ Fin 3 → ZMod 2) :
    tvMat v *ᵥ (((z : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ x) =
    ((z : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ (tvMat v *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, central_comm_matrix hz v]

theorem tv_conj_gen {zM ziM : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)}
    (hzz : ∀ w, zM *ᵥ (ziM *ᵥ w) = w)
    (hzB : ∀ x y, pairedSympForm (ZMod 2) 3 (zM *ᵥ x) (zM *ᵥ y) = pairedSympForm (ZMod 2) 3 x y)
    (hcomm : ∀ v x, tvMat v *ᵥ (zM *ᵥ x) = zM *ᵥ (tvMat v *ᵥ x)) (v w : Fin 3 ⊕ Fin 3 → ZMod 2) :
    tvMat v *ᵥ w = tvMat (zM *ᵥ v) *ᵥ w := by
  have hw := hcomm v (ziM *ᵥ w)
  rw [hzz] at hw
  rw [hw, tvMat_mulVec v (ziM *ᵥ w), Matrix.mulVec_add, Matrix.mulVec_smul, hzz,
    tvMat_mulVec (zM *ᵥ v) w]
  have hs : pairedSympForm (ZMod 2) 3 (ziM *ᵥ w) v = pairedSympForm (ZMod 2) 3 w (zM *ᵥ v) := by
    rw [← hzB (ziM *ᵥ w) v, hzz]
  rw [hs]

theorem zinv_mulVec (z : StatedSp 3 (ZMod 2)) (w : Fin 3 ⊕ Fin 3 → ZMod 2) :
    ((z : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ
    (((((z⁻¹ : StatedSp 3 (ZMod 2)) : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2))) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
    Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]

theorem tv_conj_of_comm (z : StatedSp 3 (ZMod 2))
    (hcomm : ∀ v x : Fin 3 ⊕ Fin 3 → ZMod 2,
      tvMat v *ᵥ (((z : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ x) =
      ((z : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ (tvMat v *ᵥ x))
    (v w : Fin 3 ⊕ Fin 3 → ZMod 2) :
    tvMat v *ᵥ w = tvMat (((z : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ v) *ᵥ w :=
  tv_conj_gen (zinv_mulVec z) (fun x y => pairedSympForm_mulVec z x y) hcomm v w

theorem tv_eq_of_fix (u v : Fin 3 ⊕ Fin 3 → ZMod 2) (hv : v ≠ 0)
    (h : ∀ w, tvMat v *ᵥ w = tvMat u *ᵥ w) : u = v := by
  obtain ⟨s, hs⟩ := exists_J_coord v hv
  have hw := h (Pi.single s 1)
  rw [tvMat_mulVec, tvMat_mulVec] at hw
  have hBv : pairedSympForm (ZMod 2) 3 (Pi.single s 1) v = 1 := by
    rw [pairedSympForm_eq_dot, single_dotProduct, one_mul, hs]
  have hc : pairedSympForm (ZMod 2) 3 (Pi.single s 1) v • v =
      pairedSympForm (ZMod 2) 3 (Pi.single s 1) u • u := add_left_cancel hw
  rw [hBv, one_smul] at hc
  have h01 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  by_cases hc0 : pairedSympForm (ZMod 2) 3 (Pi.single s 1) u = 0
  · rw [hc0, zero_smul] at hc
    exact absurd hc hv
  · rw [h01 _ hc0, one_smul] at hc
    exact hc.symm

theorem center_eq_one_of_mem (z : StatedSp 3 (ZMod 2))
    (hz : z ∈ Subgroup.center (StatedSp 3 (ZMod 2))) : z = 1 := by
  have hfix : ∀ v : Fin 3 ⊕ Fin 3 → ZMod 2, v ≠ 0 →
      ((z : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ v = v := by
    intro v hv
    exact tv_eq_of_fix _ v hv (tv_conj_of_comm z (central_comm_mulVec hz) v)
  have hone : ((z : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) = 1 := by
    ext i j
    have h := hfix (Pi.single j 1) (by simp [Pi.single_eq_zero_iff])
    have h2 := congrFun h i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using h2
  apply Subtype.ext
  apply Units.ext
  exact hone

theorem center_statedSp_eq_bot : Subgroup.center ↥(StatedSp 3 (ZMod 2)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  exact center_eq_one_of_mem z hz

end CFSG.RankThree.PartTwo.Late.KFParSp6

end
