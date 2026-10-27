module

public import CFSG.Quasithin.H13.AS91Sec4TwoInputs
public import CFSG.Quasithin.Background.SmithB45M22HatModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
open CFSG.Quasithin.HatM22 CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol
open scoped Matrix

@[expose] def reZ (c : FieldFour) : ZMod 2 := if c.re then 1 else 0

@[expose] def imZ (c : FieldFour) : ZMod 2 := if c.im then 1 else 0

@[expose] def ofZ (a b : ZMod 2) : FieldFour := ⟨decide (a = 1), decide (b = 1)⟩

theorem reZ_add : ∀ a b : FieldFour, reZ (a + b) = reZ a + reZ b := by decide

theorem imZ_add : ∀ a b : FieldFour, imZ (a + b) = imZ a + imZ b := by decide

theorem ofZ_reZ_imZ : ∀ c : FieldFour, ofZ (reZ c) (imZ c) = c := by decide

theorem reZ_ofZ : ∀ a b : ZMod 2, reZ (ofZ a b) = a := by decide

theorem imZ_ofZ : ∀ a b : ZMod 2, imZ (ofZ a b) = b := by decide

theorem reZ_ω_mul : ∀ c : FieldFour, reZ (ω * c) = imZ c := by decide

theorem imZ_ω_mul : ∀ c : FieldFour, imZ (ω * c) = reZ c + imZ c := by decide

@[expose] def coordV (x : Fin 6 → FieldFour) : V12 :=
  Fin.append (fun i => reZ (x i)) (fun i => imZ (x i))

theorem coordV_lo (x : Fin 6 → FieldFour) (i : Fin 6) : coordV x (lo i) = reZ (x i) :=
  Fin.append_left _ _ i

theorem coordV_hi (x : Fin 6 → FieldFour) (i : Fin 6) : coordV x (hi i) = imZ (x i) :=
  Fin.append_right _ _ i

@[expose] def vCoord (v : V12) : Fin 6 → FieldFour := fun i => ofZ (v (lo i)) (v (hi i))

theorem vCoord_coordV (x : Fin 6 → FieldFour) : vCoord (coordV x) = x :=
  funext fun i => by simp only [vCoord, coordV_lo, coordV_hi, ofZ_reZ_imZ]

theorem coordV_vCoord (v : V12) : coordV (vCoord v) = v :=
  ext_lo_hi (fun i => by rw [coordV_lo, vCoord, reZ_ofZ])
    (fun i => by rw [coordV_hi, vCoord, imZ_ofZ])

theorem coordV_add (x y : Fin 6 → FieldFour) : coordV (x + y) = coordV x + coordV y :=
  ext_lo_hi (fun i => by simp only [coordV_lo, Pi.add_apply, reZ_add])
    (fun i => by simp only [coordV_hi, Pi.add_apply, imZ_add])

theorem coordV_ω_smul (x : Fin 6 → FieldFour) : coordV (ω • x) = theta0 (coordV x) :=
  ext_lo_hi (fun i => by
      rw [coordV_lo, theta0_lo, coordV_hi, Pi.smul_apply, smul_eq_mul, reZ_ω_mul])
    (fun i => by
      rw [coordV_hi, theta0_hi, coordV_lo, coordV_hi, Pi.smul_apply, smul_eq_mul, imZ_ω_mul])

@[expose] def framePTab : Vector (Vector FieldFour 6) 6 :=
  #v[#v[1, 1, 0, ω, 0, 1],
     #v[0, 0, 1, 1, ω, 1],
     #v[0, 1, 1, 1, ω₂, ω₂],
     #v[0, 1, 1, 0, ω, ω₂],
     #v[0, 0, 0, 1, 1, ω],
     #v[0, 0, 0, 0, 1, 1]]

@[expose] def framePInvTab : Vector (Vector FieldFour 6) 6 :=
  #v[#v[1, 1, ω₂, ω, 0, ω₂],
     #v[0, 1, ω₂, ω, ω, 1],
     #v[0, 1, 0, 0, 1, ω₂],
     #v[0, 0, ω, ω, ω₂, 1],
     #v[0, 0, ω₂, ω₂, ω₂, 1],
     #v[0, 0, ω₂, ω₂, ω₂, 0]]

@[expose] def frameP : Matrix (Fin 6) (Fin 6) FieldFour := untab framePTab

@[expose] def framePInv : Matrix (Fin 6) (Fin 6) FieldFour := untab framePInvTab

theorem frameP_mul_inv : frameP * framePInv = 1 := by decide +kernel

theorem framePInv_mul : framePInv * frameP = 1 := by decide +kernel

@[expose] def frameE : (Fin 6 → FieldFour) ≃+ V12 where
  toFun x := coordV (framePInv *ᵥ x)
  invFun v := frameP *ᵥ vCoord v
  left_inv x := by
    simp only [vCoord_coordV, Matrix.mulVec_mulVec, frameP_mul_inv, Matrix.one_mulVec]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec, framePInv_mul, Matrix.one_mulVec, coordV_vCoord]
  map_add' x y := by simp only [Matrix.mulVec_add, coordV_add]

theorem frameE_apply (x : Fin 6 → FieldFour) : frameE x = coordV (framePInv *ᵥ x) := rfl

theorem frameE_ω_smul (x : Fin 6 → FieldFour) : frameE (ω • x) = theta0 (frameE x) := by
  rw [frameE_apply, frameE_apply, Matrix.mulVec_smul, coordV_ω_smul]

@[expose] def addEquivToLin {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W]
    [Module (ZMod 2) W] (e : U ≃+ W) : U ≃ₗ[ZMod 2] W :=
  { e with map_smul' := fun c x => ZMod.map_smul e c x }

@[simp] theorem addEquivToLin_apply {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W] (e : U ≃+ W) (x : U) : addEquivToLin e x = e x := rfl

@[expose] def mulVecEquiv (g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
    (Fin 6 → FieldFour) ≃+ (Fin 6 → FieldFour) where
  toFun x := (g : Matrix (Fin 6) (Fin 6) FieldFour) *ᵥ x
  invFun x := ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
    Matrix (Fin 6) (Fin 6) FieldFour) *ᵥ x
  left_inv x := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv x := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  map_add' x y := Matrix.mulVec_add _ x y

@[expose] noncomputable def frameHom :
    Matrix.GeneralLinearGroup (Fin 6) FieldFour →* (V12 ≃ₗ[ZMod 2] V12) where
  toFun g := @addEquivToLin V12 V12 Pi.addCommGroup (Pi.Function.module _ _ _) Pi.addCommGroup
    (Pi.Function.module _ _ _) ((frameE.symm.trans (mulVecEquiv g)).trans frameE)
  map_one' := LinearEquiv.ext fun v => by
    change frameE (((1 : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
      Matrix (Fin 6) (Fin 6) FieldFour) *ᵥ frameE.symm v) = v
    rw [Units.val_one, Matrix.one_mulVec, AddEquiv.apply_symm_apply]
  map_mul' g h := LinearEquiv.ext fun v => by
    change frameE (((g * h : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
      Matrix (Fin 6) (Fin 6) FieldFour) *ᵥ frameE.symm v) =
      frameE ((g : Matrix (Fin 6) (Fin 6) FieldFour) *ᵥ frameE.symm (frameE
        ((h : Matrix (Fin 6) (Fin 6) FieldFour) *ᵥ frameE.symm v)))
    rw [AddEquiv.symm_apply_apply, Units.val_mul, ← Matrix.mulVec_mulVec]

theorem frameHom_apply (g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) (v : V12) :
    frameHom g v = frameE ((g : Matrix (Fin 6) (Fin 6) FieldFour) *ᵥ frameE.symm v) := rfl

theorem frameHom_eq_linOfRows {g : Matrix.GeneralLinearGroup (Fin 6) FieldFour} {r : Array ℕ}
    (h : ∀ j : Fin 12, frameE ((g : Matrix (Fin 6) (Fin 6) FieldFour) *ᵥ
      frameE.symm (vecOf (2 ^ (j : ℕ)))) = vecOf r[(j : ℕ)]!) (v : V12) :
    frameHom g v = linOfRows r v := by
  have hf : (frameHom g : V12 →ₗ[ZMod 2] V12) = linOfRows r :=
    linMap_ext fun j => by rw [linOfRows_unit]; exact h j
  exact LinearMap.congr_fun hf v

theorem frameHom_G1 (v : V12) : frameHom hatM22G1 v = linOfRows Two.m1Rows v :=
  frameHom_eq_linOfRows (by decide +kernel) v

theorem frameHom_G2 (v : V12) : frameHom hatM22G2 v = linOfRows Two.m2Rows v :=
  frameHom_eq_linOfRows (by decide +kernel) v

theorem map_hatM22Γ₀ : hatM22Γ₀.map frameHom = genGrp Two.gamGens := by
  rw [hatM22Γ₀, MonoidHom.map_closure, genGrp]
  congr 1
  ext l
  simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, GenSet, Two.gamGens, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_setOf_eq]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, frameHom_G1⟩
    · exact ⟨_, Or.inr rfl, frameHom_G2⟩
  · rintro ⟨r, rfl | rfl, hr⟩
    · exact Or.inl (LinearEquiv.ext fun v => (hr v).trans (frameHom_G1 v).symm)
    · exact Or.inr (LinearEquiv.ext fun v => (hr v).trans (frameHom_G2 v).symm)

theorem frameHom_smul_one {g : Matrix.GeneralLinearGroup (Fin 6) FieldFour} {c : FieldFour}
    (hg : (g : Matrix (Fin 6) (Fin 6) FieldFour) = c • 1) (v : V12) :
    frameHom g v = frameE (c • frameE.symm v) := by
  rw [frameHom_apply, hg, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem frameHom_ω {g : Matrix.GeneralLinearGroup (Fin 6) FieldFour}
    (hg : (g : Matrix (Fin 6) (Fin 6) FieldFour) = ω • 1) (v : V12) : frameHom g v = theta0 v := by
  rw [frameHom_smul_one hg, frameE_ω_smul, AddEquiv.apply_symm_apply]

theorem frameHom_ω₂ {g : Matrix.GeneralLinearGroup (Fin 6) FieldFour}
    (hg : (g : Matrix (Fin 6) (Fin 6) FieldFour) = ω₂ • 1) (v : V12) :
    frameHom g v = theta0 (theta0 v) := by
  have hω : ω₂ = ω * ω := by decide
  rw [frameHom_smul_one hg, hω, mul_smul, frameE_ω_smul, frameE_ω_smul, AddEquiv.apply_symm_apply]

end CFSG.Quasithin.H13.AS91
