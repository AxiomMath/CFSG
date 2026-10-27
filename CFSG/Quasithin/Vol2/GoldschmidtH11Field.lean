module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Model

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] (a : ℕ)

omit [Finite F] in
theorem sg_ringEquiv (ψ : F ≃+* F) (x : F) : sg a (ψ x) = ψ (sg a x) :=
  (RingHom.map_iterateFrobenius ψ.toRingHom 2 x a).symm

omit [Finite F] in
theorem frobPow_map (ψ : F ≃+* F) (M : Matrix (Fin 2) (Fin 2) F) :
    frobPow a (M.map ψ) = (frobPow a M).map ψ := by
  ext i j
  simp [frobPow_apply, sg_ringEquiv]

omit [Finite F] in
theorem herm_map (ψ : F ≃+* F) (M : Matrix (Fin 2) (Fin 2) F) (hM : (frobPow a M)ᵀ = M) :
    (frobPow a (M.map ψ))ᵀ = M.map ψ := by
  rw [frobPow_map, ← Matrix.transpose_map, hM]

@[expose] def fieldFun (ψ : F ≃+* F) (v : HV F a) : HV F a :=
  mkHV a ((hm a v).map ψ) (herm_map a ψ _ (hm_herm a v))

omit [Finite F] in
theorem hm_fieldFun (ψ : F ≃+* F) (v : HV F a) : hm a (fieldFun a ψ v) = (hm a v).map ψ := rfl

omit [Finite F] in
theorem fieldFun_mul (ψ : F ≃+* F) (v w : HV F a) :
    fieldFun a ψ (v * w) = fieldFun a ψ v * fieldFun a ψ w :=
  hm_injective a (by simp only [hm_fieldFun, hm_mul]; exact Matrix.map_add _ (map_add _) _ _)

omit [Finite F] in
theorem fieldFun_fieldFun (ψ χ : F ≃+* F) (v : HV F a) :
    fieldFun a ψ (fieldFun a χ v) = fieldFun a (χ.trans ψ) v :=
  hm_injective a (by simp only [hm_fieldFun, Matrix.map_map]; rfl)

omit [Finite F] in
theorem fieldFun_refl (v : HV F a) : fieldFun a (RingEquiv.refl F) v = v :=
  hm_injective a (by simp only [hm_fieldFun]; ext i j; rfl)

@[expose] def fieldAut (ψ : F ≃+* F) : MulAut (HV F a) where
  toFun := fieldFun a ψ
  invFun := fieldFun a ψ.symm
  left_inv v := by
    show fieldFun a ψ.symm (fieldFun a ψ v) = v
    rw [fieldFun_fieldFun, RingEquiv.self_trans_symm, fieldFun_refl]
  right_inv v := by
    show fieldFun a ψ (fieldFun a ψ.symm v) = v
    rw [fieldFun_fieldFun, RingEquiv.symm_trans_self, fieldFun_refl]
  map_mul' := fieldFun_mul a ψ

omit [Finite F] in
theorem hm_fieldAut (ψ : F ≃+* F) (v : HV F a) : hm a (fieldAut a ψ v) = (hm a v).map ψ := rfl

@[expose] def fieldAutHom : (F ≃+* F) →* MulAut (HV F a) where
  toFun := fieldAut a
  map_one' := MulEquiv.ext (fieldFun_refl a)
  map_mul' ψ χ := MulEquiv.ext fun v => by
    change fieldFun a (ψ * χ) v = fieldFun a ψ (fieldFun a χ v)
    rw [fieldFun_fieldFun]; rfl

theorem fieldAut_actHom (h : Nat.card F = 2 ^ (2 * a)) (ψ : F ≃+* F) (γ : SL(2, F)) (v : HV F a) :
    fieldAut a ψ (actHom a h γ v) =
      actHom a h (Matrix.SpecialLinearGroup.map ψ.toRingHom γ) (fieldAut a ψ v) := by
  apply hm_injective a
  have e : ∀ M : Matrix (Fin 2) (Fin 2) F, M.map ψ.toRingHom = M.map ψ := fun M => rfl
  simp only [hm_fieldAut, hm_actHom, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, e, frobPow_map, Matrix.map_mul, Matrix.transpose_map]

@[expose] noncomputable def sgEquiv (h : Nat.card F = 2 ^ (2 * a)) : F ≃+* F where
  toFun := sg a
  invFun := sg a
  left_inv := sg_sg a h
  right_inv := sg_sg a h
  map_mul' := map_mul _
  map_add' := map_add _

theorem sgEquiv_apply (h : Nat.card F = 2 ^ (2 * a)) (x : F) : sgEquiv a h x = sg a x := rfl

@[expose] noncomputable def tauAut (h : Nat.card F = 2 ^ (2 * a)) : MulAut (HV F a) :=
  fieldAut a (sgEquiv a h)

theorem hm_tauAut (h : Nat.card F = 2 ^ (2 * a)) (v : HV F a) :
    hm a (tauAut a h v) = frobPow a (hm a v) := rfl

theorem tauAut_mul_self (h : Nat.card F = 2 ^ (2 * a)) : tauAut a h * tauAut a h = 1 :=
  MulEquiv.ext fun v => hm_injective a (by
    simp only [MulAut.mul_apply, hm_tauAut, frobPow_frobPow a h]; rfl)

end CFSG.Quasithin.H11
