module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutPGammaL

public section

namespace CFSG.Quasithin.H13

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.ABGLocalTools
open scoped MatrixGroups

section SL2

variable {F : Type} [Field F]

theorem coe_mulAut_eq_smul_conj_ch6 (α : MulAut SL(2, F)) (γ : PGammaL2 F)
    (hγ : semilinearAction F γ = psl2MulAutOf α) (G : GL (Fin 2) F)
    (hG : ProjGenLinGroup.mk G = γ.left) (b : SL(2, F)) :
    ∃ u : F, u ≠ 0 ∧ ((α b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      u • ((G : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F).map γ.right *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
  have h1 : ProjectiveSpecialLinearGroup.toPGL (psl2MulAutOf α (QuotientGroup.mk' _ b)) =
      ProjectiveSpecialLinearGroup.toPGL (semilinearAction F γ (QuotientGroup.mk' _ b)) := by
    rw [hγ]
  have hdecomp : γ = SemidirectProduct.inl γ.left * SemidirectProduct.inr γ.right :=
    (SemidirectProduct.inl_left_mul_inr_right γ).symm
  rw [psl2MulAutOf_mk, hdecomp, map_mul, semilinearAction_inl, semilinearAction_inr,
    MulAut.mul_apply, toPGL_pglAction, psl2FieldAut_toPGL] at h1
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (α b)) =
    γ.left * (pgl2FieldAut F) γ.right (ProjGenLinGroup.mk (SpecialLinearGroup.toGL b)) *
      γ.left⁻¹ at h1
  rw [pgl2FieldAut_apply, ← hG] at h1
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (α b)) =
    ProjGenLinGroup.mk G * pgl2RingEquiv γ.right
      (QuotientGroup.mk' _ (SpecialLinearGroup.toGL b)) * (ProjGenLinGroup.mk G)⁻¹ at h1
  rw [pgl2RingEquiv_mk] at h1
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (α b)) =
    ProjGenLinGroup.mk G * ProjGenLinGroup.mk
      (GeneralLinearGroup.map γ.right.toRingHom (SpecialLinearGroup.toGL b)) *
        (ProjGenLinGroup.mk G)⁻¹ at h1
  rw [← map_mul, ← map_inv, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at h1
  obtain ⟨w, hw⟩ := h1
  have hw' := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hw
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at hw'
  have hmap : ((GeneralLinearGroup.map γ.right.toRingHom (SpecialLinearGroup.toGL b) :
      GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (b : Matrix (Fin 2) (Fin 2) F).map γ.right :=
    rfl
  have hαb : ((SpecialLinearGroup.toGL (α b) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((α b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := rfl
  rw [hmap, hαb] at hw'
  refine ⟨(w : F)⁻¹, inv_ne_zero w.ne_zero, ?_⟩
  rw [← hw', Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
    smul_smul, inv_mul_cancel₀ w.ne_zero, one_smul]

theorem eq_one_of_sq_eq_one_ch6 [CharP F 2] {u : F} (hu : u ^ 2 = 1) : u = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h : (u + 1) * (u + 1) = 0 := by linear_combination hu + (u + 1) * h2
  have h' : u + 1 = 0 := mul_self_eq_zero.mp h
  have := eq_neg_of_add_eq_zero_left h'
  rwa [CharTwo.neg_eq] at this

theorem exists_conj_map_of_mulAut_ch6 [Finite F] [CharP F 2] (α : MulAut SL(2, F)) :
    ∃ (G : GL (Fin 2) F) (σ : F ≃+* F), ∀ b : SL(2, F),
      ((α b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (G : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F).map σ *
          ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨γ, hγ⟩ := semilinearAction_surjective F (psl2MulAutOf α)
  obtain ⟨G, hG⟩ := ProjGenLinGroup.mk_surjective γ.left
  refine ⟨G, γ.right, fun b => ?_⟩
  obtain ⟨u, -, hu⟩ := coe_mulAut_eq_smul_conj_ch6 α γ hγ G hG b
  have hdet := congrArg Matrix.det hu
  rw [(α b).2, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_mul] at hdet
  have hdG : (G : Matrix (Fin 2) (Fin 2) F).det * ((G⁻¹ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hdb : ((b : Matrix (Fin 2) (Fin 2) F).map γ.right).det = 1 := by
    rw [← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det, b.2, map_one]
  have hu2 : u ^ 2 = 1 := by
    have : u ^ 2 * ((G : Matrix (Fin 2) (Fin 2) F).det *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det) = 1 := by
      rw [hdb, mul_one] at hdet
      rw [← hdet]
    rwa [hdG, mul_one] at this
  rw [hu, eq_one_of_sq_eq_one_ch6 hu2, one_smul]

end SL2

section TwoFields

variable {F₁ F₂ : Type} [Field F₁] [Field F₂]

@[expose] noncomputable def slMapEquivCh6 (e : F₁ ≃+* F₂) : SL(2, F₁) ≃* SL(2, F₂) where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    ext i j
    simp
  right_inv A := by
    ext i j
    simp
  map_mul' := map_mul _

theorem coe_slMapEquivCh6 (e : F₁ ≃+* F₂) (A : SL(2, F₁)) :
    ((slMapEquivCh6 e A : SL(2, F₂)) : Matrix (Fin 2) (Fin 2) F₂) =
      (A : Matrix (Fin 2) (Fin 2) F₁).map e :=
  rfl

@[expose] noncomputable def glAddEquivCh6 (G : GL (Fin 2) F₁) :
    (Fin 2 → F₁) ≃+ (Fin 2 → F₁) where
  toFun v := (G : Matrix (Fin 2) (Fin 2) F₁) *ᵥ v
  invFun v := ((G⁻¹ : GL (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁) *ᵥ v
  left_inv v := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  map_add' v w := Matrix.mulVec_add _ v w

@[expose] noncomputable def vecAddEquivCh6 (e : F₁ ≃+* F₂) : (Fin 2 → F₁) ≃+ (Fin 2 → F₂) :=
  AddEquiv.piCongrRight fun _ => e.toAddEquiv

theorem vecAddEquivCh6_apply (e : F₁ ≃+* F₂) (v : Fin 2 → F₁) :
    vecAddEquivCh6 e v = e ∘ v :=
  rfl

theorem vecAddEquivCh6_mulVec (e : F₁ ≃+* F₂) (M : Matrix (Fin 2) (Fin 2) F₁)
    (v : Fin 2 → F₁) :
    vecAddEquivCh6 e (M *ᵥ v) = M.map e *ᵥ vecAddEquivCh6 e v := by
  funext i
  rw [vecAddEquivCh6_apply, vecAddEquivCh6_apply, Function.comp_apply]
  exact RingHom.map_mulVec e.toRingHom M v i

theorem exists_addEquiv_of_sl2_mulEquiv_ch6 [Finite F₁] [Finite F₂] [CharP F₁ 2]
    (hcard : Nat.card F₁ = Nat.card F₂) (θ : SL(2, F₁) ≃* SL(2, F₂)) :
    ∃ f : (Fin 2 → F₁) ≃+ (Fin 2 → F₂), ∀ (γ : SL(2, F₁)) (v : Fin 2 → F₁),
      f ((γ : Matrix (Fin 2) (Fin 2) F₁) *ᵥ v) =
        ((θ γ : SL(2, F₂)) : Matrix (Fin 2) (Fin 2) F₂) *ᵥ f v := by
  classical
  have := Fintype.ofFinite F₁
  have := Fintype.ofFinite F₂
  let e : F₁ ≃+* F₂ := FiniteField.ringEquivOfCardEq (K := F₁) (K' := F₂) (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard)
  obtain ⟨G, σ, hG⟩ := exists_conj_map_of_mulAut_ch6 (θ.trans (slMapEquivCh6 e).symm)
  refine ⟨((vecAddEquivCh6 σ).trans (glAddEquivCh6 G)).trans (vecAddEquivCh6 e),
    fun γ v => ?_⟩
  have hθ : θ γ = slMapEquivCh6 e ((θ.trans (slMapEquivCh6 e).symm) γ) := by
    rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hθm : ((θ γ : SL(2, F₂)) : Matrix (Fin 2) (Fin 2) F₂) =
      ((G : Matrix (Fin 2) (Fin 2) F₁) * (γ : Matrix (Fin 2) (Fin 2) F₁).map σ *
        ((G⁻¹ : GL (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁)).map e := by
    rw [hθ, coe_slMapEquivCh6, hG]
  simp only [AddEquiv.trans_apply]
  rw [hθm, ← vecAddEquivCh6_mulVec]
  congr 1
  change (G : Matrix (Fin 2) (Fin 2) F₁) *ᵥ
      vecAddEquivCh6 σ ((γ : Matrix (Fin 2) (Fin 2) F₁) *ᵥ v) =
    ((G : Matrix (Fin 2) (Fin 2) F₁) * (γ : Matrix (Fin 2) (Fin 2) F₁).map σ *
      ((G⁻¹ : GL (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁)) *ᵥ
        ((G : Matrix (Fin 2) (Fin 2) F₁) *ᵥ vecAddEquivCh6 σ v)
  rw [vecAddEquivCh6_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one,
    ← Matrix.mulVec_mulVec]

end TwoFields

end CFSG.Quasithin.H13
