module

public import CFSG.Quasithin.Background.HOm4Norm
public import CFSG.Quasithin.EmptyFaithful.S153G93DOm4PA

public section

namespace CFSG.Quasithin.S153G93D.Om4P

open CFSG.Quasithin.H.Om4 CFSG.Quasithin.H Matrix

variable {F : Type} [Field F]

theorem toAdd_lr_frM (A B : GL (Fin 2) F) (τ : F ≃+* F) (X : VM F) :
    Multiplicative.toAdd ((lr A B * frM τ) X) =
      (A : Matrix (Fin 2) (Fin 2) F) * (Multiplicative.toAdd X).map τ *
        (B : Matrix (Fin 2) (Fin 2) F)ᵀ := rfl

theorem conj_swap (X Y A B : GL (Fin 2) F) (τ : F ≃+* F) :
    (lr X Y * frM τ * trM) * lr A B * (lr X Y * frM τ * trM)⁻¹ =
      lr (X * GeneralLinearGroup.map τ.toRingHom B * X⁻¹)
        (Y * GeneralLinearGroup.map τ.toRingHom A * Y⁻¹) := by
  have e1 : lr (X * GeneralLinearGroup.map τ.toRingHom B * X⁻¹)
      (Y * GeneralLinearGroup.map τ.toRingHom A * Y⁻¹) * lr X Y =
      lr (X * GeneralLinearGroup.map τ.toRingHom B) (Y * GeneralLinearGroup.map τ.toRingHom A) := by
    rw [lr_mul, inv_mul_cancel_right, inv_mul_cancel_right]
  rw [mul_inv_eq_iff_eq_mul]
  calc lr X Y * frM τ * trM * lr A B = lr X Y * (frM τ * lr B A) * trM := by
        rw [mul_assoc _ trM, trM_lr]; simp only [mul_assoc]
    _ = lr X Y * (lr (GeneralLinearGroup.map τ.toRingHom B)
          (GeneralLinearGroup.map τ.toRingHom A) * frM τ) * trM := by rw [frM_lr]
    _ = lr (X * GeneralLinearGroup.map τ.toRingHom B)
          (Y * GeneralLinearGroup.map τ.toRingHom A) * frM τ * trM := by
        rw [← mul_assoc (lr X Y), lr_mul]
    _ = _ := by rw [← e1]; simp only [mul_assoc]

theorem eq_scalar_of_lr_eq {P Q : GL (Fin 2) F} (h : lr P 1 = lr 1 Q) :
    ∃ c : F, (Q : Matrix (Fin 2) (Fin 2) F) = c • 1 := by
  have key : ∀ X : Matrix (Fin 2) (Fin 2) F,
      (P : Matrix (Fin 2) (Fin 2) F) * X = X * (Q : Matrix (Fin 2) (Fin 2) F)ᵀ := by
    intro X
    have := congrArg (fun f : MulAut (VM F) => Multiplicative.toAdd (f (Multiplicative.ofAdd X))) h
    simpa [toAdd_lr] using this
  have hP : (P : Matrix (Fin 2) (Fin 2) F) = (Q : Matrix (Fin 2) (Fin 2) F)ᵀ := by
    have := key 1
    simpa using this
  have hcomm : ∀ X : Matrix (Fin 2) (Fin 2) F, Commute X (Q : Matrix (Fin 2) (Fin 2) F)ᵀ := by
    intro X
    have := key X
    rw [hP] at this
    exact this.symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single fun i j _ => hcomm _
  refine ⟨c, ?_⟩
  have h1 : (Q : Matrix (Fin 2) (Fin 2) F)ᵀ = c • 1 := by
    rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have h2 := congrArg Matrix.transpose h1
  rwa [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at h2

theorem form_of_normalizes [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) {x : MulAut (VM F)}
    (hx : x ∈ Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F))))
    (hL : ∀ g : SpecialLinearGroup (Fin 2) F, ∃ g' : SpecialLinearGroup (Fin 2) F,
      x * lg g * x⁻¹ = lg g') :
    ∃ (A B : GL (Fin 2) F) (τ : F ≃+* F), x = lr A B * frM τ := by
  obtain ⟨A, B, τ, h | h⟩ := exists_eq_of_mem_normalizer h4 hx
  · exact ⟨A, B, τ, h⟩
  · exfalso
    obtain ⟨g', hg'⟩ := hL (tv 0 1 (by decide) (1 : F))
    rw [h] at hg'
    have h1 := conj_swap A B (Matrix.SpecialLinearGroup.toGL (tv 0 1 (by decide) (1 : F))) 1 τ
    have e1 : A * GeneralLinearGroup.map τ.toRingHom (1 : GL (Fin 2) F) * A⁻¹ = 1 := by
      rw [map_one, mul_one, mul_inv_cancel]
    rw [e1] at h1
    have h2 : lr (Matrix.SpecialLinearGroup.toGL g') 1 = lr (1 : GL (Fin 2) F)
        (B * GeneralLinearGroup.map τ.toRingHom
          (Matrix.SpecialLinearGroup.toGL (tv 0 1 (by decide) (1 : F))) * B⁻¹) :=
      hg'.symm.trans h1
    obtain ⟨c, hc⟩ := eq_scalar_of_lr_eq h2
    set G : GL (Fin 2) F := GeneralLinearGroup.map τ.toRingHom
      (Matrix.SpecialLinearGroup.toGL (tv 0 1 (by decide) (1 : F))) with hGdef
    have hc' : (B : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) *
        ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = c • 1 := by
      rw [← hc, Units.val_mul, Units.val_mul]
    have e2 : ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) =
        1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hG : (G : Matrix (Fin 2) (Fin 2) F) = c • 1 := by
      calc (G : Matrix (Fin 2) (Fin 2) F)
          = ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) *
            (G : Matrix (Fin 2) (Fin 2) F) * (((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
              (B : Matrix (Fin 2) (Fin 2) F)) := by rw [e2, Matrix.one_mul, Matrix.mul_one]
        _ = ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            ((B : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) *
              ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
            (B : Matrix (Fin 2) (Fin 2) F) := by simp only [Matrix.mul_assoc]
        _ = c • 1 := by
          rw [hc', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, e2]
    have e3 : ((Matrix.SpecialLinearGroup.toGL (tv 0 1 (by decide) (1 : F)) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 0 1 = 1 := by
      change (Matrix.transvection (0 : Fin 2) 1 (1 : F)) 0 1 = 1
      simp [Matrix.transvection]
    have h01 := congrFun (congrFun hG 0) 1
    rw [hGdef, GeneralLinearGroup.map_apply, e3] at h01
    simp at h01

theorem not_scalar [CharP F 2] {A B : GL (Fin 2) F} {τ : F ≃+* F}
    (h2 : (lr A B * frM τ) * (lr A B * frM τ) = 1) (h1 : lr A B * frM τ ≠ 1) :
    ¬ (τ = 1 ∧ (∃ p : F, (A : Matrix (Fin 2) (Fin 2) F) = p • 1) ∧
      ∃ m : F, (B : Matrix (Fin 2) (Fin 2) F) = m • 1) := by
  rintro ⟨rfl, ⟨p, hp⟩, ⟨m, hm⟩⟩
  obtain ⟨a', ha'⟩ : ∃ a' : MulAut (VM F), a' = lr A B * frM 1 := ⟨_, rfl⟩
  rw [← ha'] at h2 h1
  have hk : ∀ X : VM F, a' X = Multiplicative.ofAdd ((p * m) • Multiplicative.toAdd X) := by
    intro X
    apply Multiplicative.toAdd.injective
    rw [ha', toAdd_lr_frM, hp, hm, toAdd_ofAdd]
    have : (Multiplicative.toAdd X).map (1 : F ≃+* F) = Multiplicative.toAdd X := by
      ext i j
      rfl
    rw [this]
    simp [Matrix.transpose_smul, smul_smul]
    rw [mul_comm m p]
  have hsq : (p * m) * (p * m) = 1 := by
    have := congrArg (fun f : MulAut (VM F) =>
      Multiplicative.toAdd (f (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) F)))) h2
    simp only [MulAut.mul_apply, MulAut.one_apply, toAdd_ofAdd] at this
    rw [hk, toAdd_ofAdd, hk, toAdd_ofAdd, smul_smul] at this
    have h00 := congrFun (congrFun this 0) 0
    simpa using h00
  have h22 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hpm : p * m = 1 := by
    have h3 : (p * m - 1) ^ 2 = 0 := by linear_combination hsq + (1 - p * m) * h22
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h3)
  apply h1
  refine MulEquiv.ext fun X => ?_
  rw [hk, hpm, one_smul, ofAdd_toAdd]
  rfl

theorem card_le_commV {W : Type} [CommGroup W] [Finite W] [Finite F] (e : W ≃* VM F)
    {a : MulAut W} {A B : GL (Fin 2) F} {τ : F ≃+* F} (ha : congrHom e a = lr A B * frM τ)
    (h : ¬ (τ = 1 ∧ (∃ p : F, (A : Matrix (Fin 2) (Fin 2) F) = p • 1) ∧
      ∃ m : F, (B : Matrix (Fin 2) (Fin 2) F) = m • 1)) :
    Nat.card F ^ 2 ≤ Nat.card ↥(CFSG.Quasithin.commV (Subgroup.zpowers a)) := by
  obtain ⟨ψ, hψ⟩ := exists_injective_defect (Units.ne_zero A) (Units.ne_zero B) h
  let w : (Fin 2 → F) → W := fun y => e.symm (Multiplicative.ofAdd (ψ y))
  let Φ : (Fin 2 → F) → ↥(CFSG.Quasithin.commV (Subgroup.zpowers a)) := fun y =>
    ⟨a (w y) * (w y)⁻¹, Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, w y, rfl⟩⟩
  have hΦ : Function.Injective Φ := by
    intro y y' hyy
    apply hψ
    have h1 : a (w y) * (w y)⁻¹ = a (w y') * (w y')⁻¹ := congrArg Subtype.val hyy
    have h2 := congrArg (fun z => Multiplicative.toAdd (e z)) h1
    have key : ∀ z : W, e (a z) = (lr A B * frM τ) (e z) := fun z => by
      rw [← ha, congrHom_apply, MulEquiv.symm_apply_apply]
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, key, w, MulEquiv.apply_symm_apply,
      toAdd_lr_frM, toAdd_ofAdd] at h2
    simpa [defect, sub_eq_add_neg] using h2
  calc Nat.card F ^ 2 = Nat.card (Fin 2 → F) := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    _ ≤ Nat.card ↥(CFSG.Quasithin.commV (Subgroup.zpowers a)) :=
        Nat.card_le_card_of_injective Φ hΦ

end CFSG.Quasithin.S153G93D.Om4P
