module

public import CFSG.LocalAnalysis.StandardType.PhanEStdSetting

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Match

open Matrix CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.ClassicalInvolution.Phan.PhanE

variable {Fld : Type} [Field Fld] {m : ℕ}

private lemma plh_symm_eq (ρ : Equiv.Perm (Fin (m + 1))) (hρ : ∀ i, ρ (ρ i) = i) :
    ρ.symm = ρ := by
  apply Equiv.ext
  intro j
  rw [Equiv.symm_apply_eq]
  exact (hρ j).symm

private lemma plh_eq_apply_iff (ρ : Equiv.Perm (Fin (m + 1))) (hρ : ∀ i, ρ (ρ i) = i)
    (p i : Fin (m + 1)) : p = ρ i ↔ ρ p = i := by
  have h := Equiv.apply_eq_iff_eq_symm_apply ρ (x := p) (y := i)
  rw [plh_symm_eq ρ hρ] at h
  exact h.symm

private lemma plh_permMatrix_mul_self (ρ : Equiv.Perm (Fin (m + 1)))
    (hρ : ∀ i, ρ (ρ i) = i) :
    ρ.permMatrix Fld * ρ.permMatrix Fld = 1 := by
  rw [← Matrix.permMatrix_mul]
  have h : ρ * ρ = 1 := by
    apply Equiv.ext
    intro i
    simpa using hρ i
  rw [h, Matrix.permMatrix_one]

private lemma plh_conj_apply (ρ : Equiv.Perm (Fin (m + 1))) (hρ : ∀ i, ρ (ρ i) = i)
    (X : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) :
    ρ.permMatrix Fld * X * ρ.permMatrix Fld = X.submatrix ρ ρ := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, plh_symm_eq ρ hρ]

private lemma plh_conj_single (ρ : Equiv.Perm (Fin (m + 1))) (hρ : ∀ i, ρ (ρ i) = i)
    (p q : Fin (m + 1)) (c : Fld) :
    ρ.permMatrix Fld * Matrix.single p q c * ρ.permMatrix Fld =
      Matrix.single (ρ p) (ρ q) c := by
  rw [plh_conj_apply ρ hρ (Matrix.single p q c)]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.single_apply,
    plh_eq_apply_iff ρ hρ p i, plh_eq_apply_iff ρ hρ q j]

@[expose] noncomputable def permSL [CharP Fld 2] (ρ : Equiv.Perm (Fin (m + 1))) :
    SpecialLinearGroup (Fin (m + 1)) Fld :=
  ⟨ρ.permMatrix Fld, by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h <;>
      rw [h] <;> simp [CharTwo.neg_eq]⟩

theorem coe_permSL [CharP Fld 2] (ρ : Equiv.Perm (Fin (m + 1))) :
    ((permSL ρ : SpecialLinearGroup (Fin (m + 1)) Fld) : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) =
      ρ.permMatrix Fld :=
  rfl

private lemma plh_permSL_mul_self [CharP Fld 2] (ρ : Equiv.Perm (Fin (m + 1)))
    (hρ : ∀ i, ρ (ρ i) = i) :
    permSL (Fld := Fld) ρ * permSL (Fld := Fld) ρ = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_permSL, Matrix.SpecialLinearGroup.coe_one,
    plh_permMatrix_mul_self ρ hρ, Matrix.one_apply]

private lemma plh_conj_tv [CharP Fld 2] (ρ : Equiv.Perm (Fin (m + 1)))
    (hρ : ∀ i, ρ (ρ i) = i) (p q : Fin (m + 1)) (c : Fld) :
    permSL ρ * tv Fld p q c * (permSL ρ)⁻¹ = tv Fld (ρ p) (ρ q) c := by
  by_cases hpq : p = q
  · subst hpq
    simp [tv]
  · have hρpq : ρ p ≠ ρ q := fun h => hpq (ρ.injective h)
    rw [tv_of_ne hpq, tv_of_ne hρpq]
    have hinv : (permSL (Fld := Fld) ρ)⁻¹ = permSL (Fld := Fld) ρ :=
      (eq_inv_of_mul_eq_one_right (plh_permSL_mul_self ρ hρ)).symm
    rw [hinv]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (ρ.permMatrix Fld * (1 + Matrix.single p q c) * ρ.permMatrix Fld) i j =
      (1 + Matrix.single (ρ p) (ρ q) c) i j
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.add_apply,
      plh_permMatrix_mul_self ρ hρ, plh_conj_single ρ hρ p q c]

private lemma plh_map_transvection (θ : Fld →+* Fld) {p q : Fin (m + 1)}
    (h : p ≠ q) (c : Fld) :
    Matrix.SpecialLinearGroup.map θ (Matrix.SpecialLinearGroup.transvection h c) =
      Matrix.SpecialLinearGroup.transvection h (θ c) := by
  have hmat : ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) +
      Matrix.single p q c).map θ =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) + Matrix.single p q (θ c) := by
    rw [Matrix.map_add θ θ.map_add, Matrix.map_one θ θ.map_zero θ.map_one,
      Matrix.map_single p q c θ]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  exact congrArg (fun M => M i j) hmat

private lemma plh_map_tv (θ : Fld →+* Fld) (p q : Fin (m + 1)) (c : Fld) :
    Matrix.SpecialLinearGroup.map θ (tv Fld p q c) = tv Fld p q (θ c) := by
  by_cases hpq : p = q
  · subst hpq
    simp [tv]
  · rw [tv_of_ne hpq, tv_of_ne hpq]
    exact plh_map_transvection θ hpq c

private lemma plh_transpose_transvection {p q : Fin (m + 1)} (h : p ≠ q) (c : Fld) :
    Matrix.SpecialLinearGroup.transpose (Matrix.SpecialLinearGroup.transvection h c) =
      Matrix.SpecialLinearGroup.transvection h.symm c := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]

private lemma plh_inv_transvection [CharP Fld 2] {p q : Fin (m + 1)} (h : p ≠ q) (c : Fld) :
    (Matrix.SpecialLinearGroup.transvection h c)⁻¹ =
      Matrix.SpecialLinearGroup.transvection h c := by
  have hsq : Matrix.SpecialLinearGroup.transvection h c *
      Matrix.SpecialLinearGroup.transvection h c = 1 := by
    rw [← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
      Matrix.SpecialLinearGroup.transvection_coeff_zero]
  exact (eq_inv_of_mul_eq_one_right hsq).symm

private lemma plh_slSigma_tv [CharP Fld 2] (θ : Fld →+* Fld) (p q : Fin (m + 1))
    (c : Fld) : slSigma θ (m + 1) (tv Fld p q c) = tv Fld q p (θ c) := by
  by_cases hpq : p = q
  · subst hpq
    simp [tv]
  · have hqp : q ≠ p := Ne.symm hpq
    rw [tv_of_ne hpq, tv_of_ne hqp]
    show (Matrix.SpecialLinearGroup.transpose
        (Matrix.SpecialLinearGroup.map θ (Matrix.SpecialLinearGroup.transvection hpq c)))⁻¹ =
      Matrix.SpecialLinearGroup.transvection hqp (θ c)
    rw [plh_map_transvection θ hpq c, plh_transpose_transvection hpq (θ c),
      plh_inv_transvection hqp (θ c)]

theorem permSL_conj_map_tv [CharP Fld 2] (θ : Fld →+* Fld) (ρ : Equiv.Perm (Fin (m + 1)))
    (hρ : ∀ i, ρ (ρ i) = i) (p q : Fin (m + 1)) (c : Fld) :
    permSL ρ * Matrix.SpecialLinearGroup.map θ (tv Fld p q c) * (permSL ρ)⁻¹ =
      tv Fld (ρ p) (ρ q) (θ c) := by
  rw [plh_map_tv θ p q c]
  exact plh_conj_tv ρ hρ p q (θ c)

theorem permSL_conj_sigma_tv [CharP Fld 2] (θ : Fld →+* Fld) (ρ : Equiv.Perm (Fin (m + 1)))
    (hρ : ∀ i, ρ (ρ i) = i) (p q : Fin (m + 1)) (c : Fld) :
    permSL ρ * slSigma θ (m + 1) (tv Fld p q c) * (permSL ρ)⁻¹ =
      tv Fld (ρ q) (ρ p) (θ c) := by
  rw [plh_slSigma_tv θ p q c]
  exact plh_conj_tv ρ hρ q p (θ c)

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
