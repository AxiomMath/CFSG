module

public import CFSG.RankThree.PartOne.KFOUT3.Blocks

public section

namespace CFSG.RankThree.PartOne.KFOUT3

section Perm

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def permSL (σ : Equiv.Perm (Fin 3)) : SL3 K :=
  ⟨(σ⁻¹).permMatrix K, by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h
    · simp [h]
    · simp [h, CharTwo.neg_eq]⟩

theorem coe_permSL (σ : Equiv.Perm (Fin 3)) :
    ((permSL σ : SL3 K) : Matrix (Fin 3) (Fin 3) K) = (σ⁻¹).permMatrix K := rfl

theorem permSL_inv (σ : Equiv.Perm (Fin 3)) : (permSL σ : SL3 K)⁻¹ = permSL σ⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_permSL, coe_permSL, inv_inv, ← Matrix.permMatrix_mul,
    mul_inv_cancel, Matrix.permMatrix_one]
  rfl

theorem ent_permSL_conj (σ : Equiv.Perm (Fin 3)) (x : SL3 K) (a b : Fin 3) :
    ent (permSL σ * x * (permSL σ)⁻¹) a b = ent x (σ⁻¹ a) (σ⁻¹ b) := by
  rw [permSL_inv]
  simp only [ent, Matrix.SpecialLinearGroup.coe_mul, coe_permSL, inv_inv]
  have h1 : (σ⁻¹).permMatrix K * (x : Matrix (Fin 3) (Fin 3) K) =
      (x : Matrix (Fin 3) (Fin 3) K).submatrix (σ⁻¹ : Equiv.Perm (Fin 3)) id :=
    PEquiv.toMatrix_toPEquiv_mul _ _
  have h2 : ((x : Matrix (Fin 3) (Fin 3) K).submatrix (σ⁻¹ : Equiv.Perm (Fin 3)) id) *
      σ.permMatrix K = ((x : Matrix (Fin 3) (Fin 3) K).submatrix
        (σ⁻¹ : Equiv.Perm (Fin 3)) id).submatrix id σ.symm :=
    PEquiv.mul_toMatrix_toPEquiv _ _
  rw [h1, h2]
  simp [Equiv.Perm.inv_def]

theorem permSL_conj_rt (σ : Equiv.Perm (Fin 3)) {i j : Fin 3} (h : i ≠ j) (s : K) :
    permSL σ * rt h s * (permSL σ)⁻¹ = rt (σ.injective.ne h) s := by
  refine ent_ext fun a b => ?_
  rw [ent_permSL_conj, ent_rt, ent_rt]
  have e1 : σ⁻¹ a = σ⁻¹ b ↔ a = b := (σ⁻¹).injective.eq_iff
  have e2 : i = σ⁻¹ a ↔ σ i = a := Equiv.Perm.eq_inv_iff_eq
  have e3 : j = σ⁻¹ b ↔ σ j = b := Equiv.Perm.eq_inv_iff_eq
  simp only [e1, e2, e3]

@[expose] def gam : SL3 K →* SL3 K where
  toFun x := Matrix.SpecialLinearGroup.transpose x⁻¹
  map_one' := Subtype.ext (by simp [Matrix.SpecialLinearGroup.transpose])
  map_mul' x y := Subtype.ext (by
    simp only [mul_inv_rev, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul])

omit [CharP K 2] in
theorem coe_gam (x : SL3 K) :
    ((gam x : SL3 K) : Matrix (Fin 3) (Fin 3) K) = Matrix.transpose ((x⁻¹ : SL3 K) : Matrix (Fin 3) (Fin 3) K) :=
  rfl

omit [CharP K 2] in
theorem gam_gam (x : SL3 K) : gam (gam x) = x := by
  set y := gam x with hy
  have h1 : y * Matrix.SpecialLinearGroup.transpose x = 1 := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, hy, coe_gam, Matrix.SpecialLinearGroup.coe_transpose,
      ← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  have h2 : y⁻¹ = Matrix.SpecialLinearGroup.transpose x := inv_eq_of_mul_eq_one_right h1
  show Matrix.SpecialLinearGroup.transpose y⁻¹ = x
  rw [h2]
  exact Subtype.ext (by simp [Matrix.SpecialLinearGroup.transpose])

theorem gam_rt {i j : Fin 3} (h : i ≠ j) (s : K) : gam (rt h s) = rt h.symm s := by
  refine ent_ext fun a b => ?_
  show ent (gam (rt h s)) a b = _
  simp only [ent, coe_gam, Matrix.transpose_apply, Matrix.SpecialLinearGroup.transvection_inv,
    CharTwo.neg_eq]
  rw [rt_apply, rt_apply]
  by_cases hab : a = b
  · subst hab
    simp [and_comm]
  · simp [hab, eq_comm, and_comm]

omit [CharP K 2] in
theorem gam_mem_center {z : SL3 K} (hz : z ∈ Subgroup.center (SL3 K)) :
    gam z ∈ Subgroup.center (SL3 K) := by
  obtain ⟨r, hr, hzr⟩ := exists_scalar_of_mem_center (Subgroup.inv_mem _ hz)
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨r, by simpa using hr, ?_⟩
  rw [coe_gam, hzr]
  simp [Matrix.scalar_apply, Matrix.diagonal_transpose]

@[expose] def gamEquiv : SL3 K ≃* SL3 K :=
  MonoidHom.toMulEquiv gam gam (MonoidHom.ext gam_gam) (MonoidHom.ext gam_gam)

omit [CharP K 2] in
theorem map_center_gam :
    (Subgroup.center (SL3 K)).map (gamEquiv : SL3 K ≃* SL3 K).toMonoidHom =
      Subgroup.center (SL3 K) := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact gam_mem_center hz
  · intro z hz
    exact ⟨gam z, gam_mem_center hz, gam_gam z⟩

@[expose] def gamma : PSL3 K ≃* PSL3 K :=
  QuotientGroup.congr _ _ gamEquiv map_center_gam

omit [CharP K 2] in
theorem gamma_mk (x : SL3 K) : gamma (QuotientGroup.mk x) = QuotientGroup.mk (gam x) := rfl

@[expose] noncomputable def cPerm (σ : Equiv.Perm (Fin 3)) : PSL3 K ≃* PSL3 K :=
  MulAut.conj (QuotientGroup.mk (permSL σ) : PSL3 K)

theorem cPerm_mk (σ : Equiv.Perm (Fin 3)) (x : SL3 K) :
    cPerm σ (QuotientGroup.mk x) = QuotientGroup.mk (permSL σ * x * (permSL σ)⁻¹) := by
  simp [cPerm, MulAut.conj_apply]

@[expose] def permB (σ : Equiv.Perm (Fin 3)) (b : Blk) : Blk :=
  ⟨(σ b.1.1, σ b.1.2), fun h => b.2 (σ.injective h)⟩

@[expose] def swapB (b : Blk) : Blk := ⟨(b.1.2, b.1.1), b.2.symm⟩

theorem permB_permB (σ : Equiv.Perm (Fin 3)) (b : Blk) : permB σ⁻¹ (permB σ b) = b := by
  apply Subtype.ext
  simp [permB]

theorem swapB_swapB (b : Blk) : swapB (swapB b) = b := rfl

theorem rho_false (π : Equiv.Perm (Fin 3)) (b : Blk) : rho π false b = permB π b := rfl

theorem rho_true (π : Equiv.Perm (Fin 3)) (b : Blk) : rho π true b = permB π (swapB b) := rfl

theorem cPerm_RB (σ : Equiv.Perm (Fin 3)) (b : Blk) (s : K) :
    cPerm σ (RB b s) = RB (permB σ b) s := by
  rw [RB, cPerm_mk, permSL_conj_rt]
  rfl

theorem gamma_RB (b : Blk) (s : K) : gamma (RB b s) = RB (swapB b) s := by
  rw [RB, gamma_mk, gam_rt]
  rfl

@[expose] def gammaPow : Bool → (PSL3 K ≃* PSL3 K)
  | true => gamma
  | false => MulEquiv.refl _

theorem gammaPow_RB (ε : Bool) (b : Blk) (s : K) :
    gammaPow ε (RB b s) = RB (cond ε (swapB b) b) s := by
  cases ε
  · rfl
  · exact gamma_RB b s

omit [CharP K 2] in
theorem gammaPow_gammaPow (ε : Bool) (u : PSL3 K) : gammaPow ε (gammaPow ε u) = u := by
  cases ε
  · rfl
  · induction u using QuotientGroup.induction_on with
    | H x => rw [gammaPow, gamma_mk, gamma_mk, gam_gam]

theorem cPerm_cPerm_inv (σ : Equiv.Perm (Fin 3)) (u : PSL3 K) : cPerm σ (cPerm σ⁻¹ u) = u := by
  induction u using QuotientGroup.induction_on with
  | H x =>
    rw [cPerm_mk, cPerm_mk, ← permSL_inv σ]
    congr 1
    group

end Perm

end CFSG.RankThree.PartOne.KFOUT3
