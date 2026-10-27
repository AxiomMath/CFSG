module

public import CFSG.RankThree.GF2n.Smith81.S81UDict
public import CFSG.RankThree.GF2n.Smith81.S81NModel3
public import CFSG.RankThree.GF2n.Smith81.S81URoot

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

private theorem h62_tInv3_matrix : ((tInv3 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
    Matrix.transvection (0 : Fin 6) 1 1 * Matrix.transvection (2 : Fin 6) 3 1 *
      Matrix.transvection (4 : Fin 6) 5 1 := by
  simp only [tInv3, tInv2, tInv1, Units.val_mul, transvGL_val]

private theorem h62_tv_unitary (hσ : ∀ c, σ (σ c) = c) {a b : Fin 6} (hb : b = partner a)
    {c : F} (hc : σ c = c) :
    conjTr σ (Matrix.transvection a b c) * hypGram F * Matrix.transvection a b c = hypGram F := by
  subst hb
  exact transvection_long_unitary hσ a hc

private theorem h62_unitary_mul {A B : Matrix (Fin 6) (Fin 6) F}
    (hA : conjTr σ A * hypGram F * A = hypGram F) (hB : conjTr σ B * hypGram F * B = hypGram F) :
    conjTr σ (A * B) * hypGram F * (A * B) = hypGram F := by
  rw [conjTr_mul]
  calc conjTr σ B * conjTr σ A * hypGram F * (A * B)
      = conjTr σ B * (conjTr σ A * hypGram F * A) * B := by simp only [Matrix.mul_assoc]
    _ = conjTr σ B * hypGram F * B := by rw [hA]
    _ = hypGram F := hB

theorem tInv3_unitary (hσ : ∀ c, σ (σ c) = c) :
    conjTr σ ((tInv3 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * hypGram F *
      ((tInv3 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = hypGram F := by
  rw [h62_tInv3_matrix]
  exact h62_unitary_mul (h62_unitary_mul
    (h62_tv_unitary hσ (a := (0 : Fin 6)) (b := 1) (by decide) (map_one σ))
    (h62_tv_unitary hσ (a := (2 : Fin 6)) (b := 3) (by decide) (map_one σ)))
    (h62_tv_unitary hσ (a := (4 : Fin 6)) (b := 5) (by decide) (map_one σ))

theorem tInv3_det : ((tInv3 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 := by
  rw [h62_tInv3_matrix, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transvection_of_ne (0 : Fin 6) 1 (by decide) 1,
    Matrix.det_transvection_of_ne (2 : Fin 6) 3 (by decide) 1,
    Matrix.det_transvection_of_ne (4 : Fin 6) 5 (by decide) 1, mul_one, mul_one]

@[expose] noncomputable def tSU3 (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) : SUid σ 6 :=
  ⟨frameGL σ ω hω * tInv3 F * (frameGL σ ω hω)⁻¹,
    frame_conj_mem_SUid hσ.invol hω tInv3_det (tInv3_unitary hσ.invol)⟩

private theorem h62_rho_mul_apply (g g' : GL (Fin 6) F) (v : Cube F) :
    rho F (g * g') v = rho F g (rho F g' v) := by
  rw [rho_mul, Module.End.mul_apply]

private theorem h62_conj_apply (g h : GL (Fin 6) F) (v : Cube F) :
    rho F (g * h * g⁻¹) v = rho F g (rho F h (rho F g⁻¹ v)) := by
  rw [h62_rho_mul_apply, h62_rho_mul_apply]

private theorem h62_inv_rho (g : GL (Fin 6) F) (v : Cube F) : rho F g⁻¹ (rho F g v) = v := by
  rw [← Module.End.mul_apply, ← rho_mul, inv_mul_cancel, rho_one, Module.End.one_apply]

private theorem h62_rho_inv_rho (g : GL (Fin 6) F) (v : Cube F) : rho F g (rho F g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← rho_mul, mul_inv_cancel, rho_one, Module.End.one_apply]

private theorem h62_conj_rho (g h : GL (Fin 6) F) (v : Cube F) :
    rho F (g * h * g⁻¹) (rho F g v) = rho F g (rho F h v) := by
  rw [h62_conj_apply, h62_inv_rho]

theorem tSU3_CR_F (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (η : Cube F)
    (hη : rho F (tSU3 hσ hω : GL (Fin 6) F) η = η) :
    ∃ η' : Cube F, η = rho F (tSU3 hσ hω : GL (Fin 6) F) η' - η' := by
  have ht : (tSU3 hσ hω : GL (Fin 6) F) = frameGL σ ω hω * tInv3 F * (frameGL σ ω hω)⁻¹ := rfl
  rw [ht] at hη ⊢
  have hfix : rho F (tInv3 F) (rho F (frameGL σ ω hω)⁻¹ η) = rho F (frameGL σ ω hω)⁻¹ η := by
    calc rho F (tInv3 F) (rho F (frameGL σ ω hω)⁻¹ η)
        = rho F (frameGL σ ω hω)⁻¹ (rho F (frameGL σ ω hω)
            (rho F (tInv3 F) (rho F (frameGL σ ω hω)⁻¹ η))) := (h62_inv_rho _ _).symm
      _ = rho F (frameGL σ ω hω)⁻¹ η := by rw [← h62_conj_apply, hη]
  have hker : (rho F (tInv3 F) - 1) (rho F (frameGL σ ω hω)⁻¹ η) = 0 := by
    rw [LinearMap.sub_apply, Module.End.one_apply, hfix, sub_self]
  obtain ⟨ζ', hζ'⟩ :=
    LinearMap.mem_range.mp (model3_CR (K := F) (LinearMap.mem_ker.mpr hker))
  refine ⟨rho F (frameGL σ ω hω) ζ', ?_⟩
  have h2 : rho F (tInv3 F) ζ' - ζ' = rho F (frameGL σ ω hω)⁻¹ η := by
    rw [← hζ', LinearMap.sub_apply, Module.End.one_apply]
  rw [h62_conj_rho, ← map_sub, h2, h62_rho_inv_rho]

private theorem h62_long_mem (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) {a b : Fin 6}
    (hb : b = partner a) (hab : a ≠ b) {c : F} (hc : σ c = c) :
    frameGL σ ω hω * transvGL F a b hab c * (frameGL σ ω hω)⁻¹ ∈ SUid σ 6 := by
  subst hb
  exact frameConj_long_mem hσ hω a hc

private theorem h62_tv_e_self {i j : Fin 6} (hij : i ≠ j) (c : F) :
    ((transvGL F i j hij c : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ e F j =
      e F j + c • e F i := by
  rw [transvGL_val, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_single_one]
  funext k
  by_cases hki : k = i
  · subst hki
    simp [Matrix.single_apply, Matrix.col_apply, e, Pi.single_apply]
  · simp [Matrix.single_apply, Matrix.col_apply, e, Pi.single_apply, hki, Ne.symm hki]

private theorem h62_tv_e_of_ne {i j m : Fin 6} (hij : i ≠ j) (c : F) (hm : m ≠ j) :
    ((transvGL F i j hij c : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ e F m = e F m := by
  rw [transvGL_val, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_single_one]
  funext k
  simp [Matrix.single_apply, Matrix.col_apply, Ne.symm hm, e, Pi.single_apply]

private theorem h62_sw_a (a b : Fin 6) (hab : a ≠ b) (hba : b ≠ a) :
    ((transvGL F a b hab 1 * transvGL F b a hba 1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ
      e F a = e F b := by
  have hh : e F a + e F a = 0 := by
    have h2 : (2 : F) • e F a = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
    rwa [two_smul] at h2
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, h62_tv_e_self hba 1, Matrix.mulVec_add,
    Matrix.mulVec_smul, h62_tv_e_of_ne hab 1 hab, h62_tv_e_self hab 1, one_smul, one_smul]
  calc e F a + (e F b + e F a) = e F b + (e F a + e F a) := by abel
    _ = e F b := by rw [hh, add_zero]

private theorem h62_sw_other (a b m : Fin 6) (hab : a ≠ b) (hba : b ≠ a) (hma : m ≠ a)
    (hmb : m ≠ b) :
    ((transvGL F a b hab 1 * transvGL F b a hba 1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ
      e F m = e F m := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, h62_tv_e_of_ne hba 1 hma,
    h62_tv_e_of_ne hab 1 hmb]

private theorem h62_X_e0 :
    (((transvGL F 0 1 (by decide) 1 * transvGL F 1 0 (by decide) 1) *
      (transvGL F 2 3 (by decide) 1 * transvGL F 3 2 (by decide) 1) *
      (transvGL F 4 5 (by decide) 1 * transvGL F 5 4 (by decide) 1) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) *ᵥ e F 0 = e F 1 := by
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    h62_sw_other 4 5 0 (by decide) (by decide) (by decide) (by decide),
    h62_sw_other 2 3 0 (by decide) (by decide) (by decide) (by decide),
    h62_sw_a 0 1 (by decide) (by decide)]

private theorem h62_X_e2 :
    (((transvGL F 0 1 (by decide) 1 * transvGL F 1 0 (by decide) 1) *
      (transvGL F 2 3 (by decide) 1 * transvGL F 3 2 (by decide) 1) *
      (transvGL F 4 5 (by decide) 1 * transvGL F 5 4 (by decide) 1) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) *ᵥ e F 2 = e F 3 := by
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    h62_sw_other 4 5 2 (by decide) (by decide) (by decide) (by decide),
    h62_sw_a 2 3 (by decide) (by decide),
    h62_sw_other 0 1 3 (by decide) (by decide) (by decide) (by decide)]

private theorem h62_X_e4 :
    (((transvGL F 0 1 (by decide) 1 * transvGL F 1 0 (by decide) 1) *
      (transvGL F 2 3 (by decide) 1 * transvGL F 3 2 (by decide) 1) *
      (transvGL F 4 5 (by decide) 1 * transvGL F 5 4 (by decide) 1) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) *ᵥ e F 4 = e F 5 := by
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    h62_sw_a 4 5 (by decide) (by decide),
    h62_sw_other 2 3 5 (by decide) (by decide) (by decide) (by decide),
    h62_sw_other 0 1 5 (by decide) (by decide) (by decide) (by decide)]

private theorem h62_X_rho_p0 :
    rho F ((transvGL F 0 1 (by decide) 1 * transvGL F 1 0 (by decide) 1) *
      (transvGL F 2 3 (by decide) 1 * transvGL F 3 2 (by decide) 1) *
      (transvGL F 4 5 (by decide) 1 * transvGL F 5 4 (by decide) 1)) (p0 F) =
      ub F 1 3 5 (by decide) (by decide) := by
  have hub : ub F 1 3 5 (by decide) (by decide) = ιMulti F 3 ![e F 1, e F 3, e F 5] :=
    (ι3_e_eq_cubeBasis (K := F) (a := 1) (b := 3) (c := 5) (by decide) (by decide) (by decide)
      (tripleSet 1 3 5 (by decide) (by decide) (by decide)) rfl).symm
  rw [p0_eq, rho_ιMulti, hub]
  congr 1
  funext s
  fin_cases s
  · exact h62_X_e0
  · exact h62_X_e2
  · exact h62_X_e4

private theorem h62_X_mem (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) :
    frameGL σ ω hω * ((transvGL F 0 1 (by decide) 1 * transvGL F 1 0 (by decide) 1) *
      (transvGL F 2 3 (by decide) 1 * transvGL F 3 2 (by decide) 1) *
      (transvGL F 4 5 (by decide) 1 * transvGL F 5 4 (by decide) 1)) * (frameGL σ ω hω)⁻¹ ∈
      SUid σ 6 := by
  have h01 := h62_long_mem hσ hω (a := 0) (b := 1) (by decide) (by decide) (map_one σ)
  have h10 := h62_long_mem hσ hω (a := 1) (b := 0) (by decide) (by decide) (map_one σ)
  have h23 := h62_long_mem hσ hω (a := 2) (b := 3) (by decide) (by decide) (map_one σ)
  have h32 := h62_long_mem hσ hω (a := 3) (b := 2) (by decide) (by decide) (map_one σ)
  have h45 := h62_long_mem hσ hω (a := 4) (b := 5) (by decide) (by decide) (map_one σ)
  have h54 := h62_long_mem hσ hω (a := 5) (b := 4) (by decide) (by decide) (map_one σ)
  have e : frameGL σ ω hω * ((transvGL F 0 1 (by decide) 1 * transvGL F 1 0 (by decide) 1) *
      (transvGL F 2 3 (by decide) 1 * transvGL F 3 2 (by decide) 1) *
      (transvGL F 4 5 (by decide) 1 * transvGL F 5 4 (by decide) 1)) * (frameGL σ ω hω)⁻¹ =
      (frameGL σ ω hω * transvGL F 0 1 (by decide) 1 * (frameGL σ ω hω)⁻¹) *
        (frameGL σ ω hω * transvGL F 1 0 (by decide) 1 * (frameGL σ ω hω)⁻¹) *
        ((frameGL σ ω hω * transvGL F 2 3 (by decide) 1 * (frameGL σ ω hω)⁻¹) *
          (frameGL σ ω hω * transvGL F 3 2 (by decide) 1 * (frameGL σ ω hω)⁻¹)) *
        ((frameGL σ ω hω * transvGL F 4 5 (by decide) 1 * (frameGL σ ω hω)⁻¹) *
          (frameGL σ ω hω * transvGL F 5 4 (by decide) 1 * (frameGL σ ω hω)⁻¹)) := by
    group
  rw [e]
  exact mul_mem (mul_mem (mul_mem h01 h10) (mul_mem h23 h32)) (mul_mem h45 h54)

private theorem h62_key (ω : F) (hω : ω + σ ω = 1) (X : GL (Fin 6) F) (v : Cube F)
    (hv : rho F X (p0 F) = v) :
    rho F (frameGL σ ω hω) v = rho F (frameGL σ ω hω * X * (frameGL σ ω hω)⁻¹) (pt0 F) := by
  rw [← hv]
  calc rho F (frameGL σ ω hω) (rho F X (p0 F))
      = rho F (frameGL σ ω hω * X) (p0 F) := (h62_rho_mul_apply _ _ _).symm
    _ = rho F (frameGL σ ω hω * X * (frameGL σ ω hω)⁻¹ * frameGL σ ω hω) (p0 F) := by
        rw [inv_mul_cancel_right]
    _ = rho F (frameGL σ ω hω * X * (frameGL σ ω hω)⁻¹) (rho F (frameGL σ ω hω) (p0 F)) :=
        h62_rho_mul_apply _ _ _
    _ = rho F (frameGL σ ω hω * X * (frameGL σ ω hω)⁻¹) (pt0 F) := by rw [rho_frameGL_p0]

theorem rootPt_u135 (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) :
    rho F (frameGL σ ω hω) (ub F 1 3 5 (by decide) (by decide)) ∈ RootPt σ := by
  rw [h62_key ω hω _ _ h62_X_rho_p0]
  exact rho_mem_RootPt (h62_X_mem hσ hω) pt0_mem_RootPt

private theorem h62_beta_ub_zero {a b d p q r : Fin 6} (hab : a < b) (hbd : b < d)
    (hpq : p < q) (hqr : q < r) (h : ¬ Disjoint ({a, b, d} : Finset (Fin 6)) {p, q, r}) :
    beta F (ub F a b d hab hbd) (ub F p q r hpq hqr) = 0 := by
  unfold ub
  exact beta_cubeBasis_of_not_disjoint h

private theorem h62_beta_ub_ne_zero {a b d p q r : Fin 6} (hab : a < b) (hbd : b < d)
    (hpq : p < q) (hqr : q < r) (h : Disjoint ({a, b, d} : Finset (Fin 6)) {p, q, r}) :
    beta F (ub F a b d hab hbd) (ub F p q r hpq hqr) ≠ 0 := by
  unfold ub
  exact beta_cubeBasis_ne_zero_of_disjoint h

private theorem h62_beta_t3_ub135 :
    beta F (rho F (tInv3 F) (ub F 1 3 5 (by decide) (by decide)))
      (ub F 1 3 5 (by decide) (by decide)) ≠ 0 := by
  rw [model3_rho_ub135]
  have z1 : beta F (ub F 1 3 5 (by decide) (by decide)) (ub F 1 3 5 (by decide) (by decide)) = 0 :=
    h62_beta_ub_zero (by decide) (by decide) (by decide) (by decide) (by decide)
  have z2 : beta F (ub F 0 2 5 (by decide) (by decide)) (ub F 1 3 5 (by decide) (by decide)) = 0 :=
    h62_beta_ub_zero (by decide) (by decide) (by decide) (by decide) (by decide)
  have z3 : beta F (ub F 0 3 4 (by decide) (by decide)) (ub F 1 3 5 (by decide) (by decide)) = 0 :=
    h62_beta_ub_zero (by decide) (by decide) (by decide) (by decide) (by decide)
  have z4 : beta F (ub F 0 3 5 (by decide) (by decide)) (ub F 1 3 5 (by decide) (by decide)) = 0 :=
    h62_beta_ub_zero (by decide) (by decide) (by decide) (by decide) (by decide)
  have z5 : beta F (ub F 1 2 4 (by decide) (by decide)) (ub F 1 3 5 (by decide) (by decide)) = 0 :=
    h62_beta_ub_zero (by decide) (by decide) (by decide) (by decide) (by decide)
  have z6 : beta F (ub F 1 2 5 (by decide) (by decide)) (ub F 1 3 5 (by decide) (by decide)) = 0 :=
    h62_beta_ub_zero (by decide) (by decide) (by decide) (by decide) (by decide)
  have z7 : beta F (ub F 1 3 4 (by decide) (by decide)) (ub F 1 3 5 (by decide) (by decide)) = 0 :=
    h62_beta_ub_zero (by decide) (by decide) (by decide) (by decide) (by decide)
  have hne : beta F (ub F 0 2 4 (by decide) (by decide)) (ub F 1 3 5 (by decide) (by decide)) ≠ 0 :=
    h62_beta_ub_ne_zero (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [map_add, LinearMap.add_apply, z1, z2, z3, z4, z5, z6, z7, zero_add, add_zero]
  exact hne

theorem beta_tSU3_ne (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) :
    beta F (rho F (tSU3 hσ hω : GL (Fin 6) F) (rho F (frameGL σ ω hω) (ub F 1 3 5 (by decide) (by decide))))
      (rho F (frameGL σ ω hω) (ub F 1 3 5 (by decide) (by decide))) ≠ 0 := by
  have ht : (tSU3 hσ hω : GL (Fin 6) F) = frameGL σ ω hω * tInv3 F * (frameGL σ ω hω)⁻¹ := rfl
  have hdet : ((frameGL σ ω hω : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (frameGL σ ω hω).isUnit).ne_zero
  rw [ht, h62_conj_rho, beta_rho]
  exact mul_ne_zero hdet h62_beta_t3_ub135

theorem involModel3_tSU3 (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) :
    UInvolModel3 σ (tSU3 hσ hω) := by
  refine ⟨CR_of_F hσ _ (fun η hη => tSU3_CR_F hσ hω η hη), ?_⟩
  have hp := rootPt_u135 hσ hω
  exact beta_ne_of_root hσ (tSU3 hσ hω) ⟨_, mem_Wform_iff.mpr hp.1⟩ hp (beta_tSU3_ne hσ hω)

end CFSG.RankThree.GF2n.Smith81.U6Cube
