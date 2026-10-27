module

public import CFSG.Monster.Existence.Co1BridgeData
public import CFSG.Monster.VisQuot.Simple
public import CFSG.Sporadic.Co1
import all CFSG.Blueprint.NativeSporadic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.Co1Bridge

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.Visible
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

noncomputable abbrev eMat : Matrix (Fin 24) (Fin 24) (ZMod 2) := rowsMatrix 24 eRows

noncomputable abbrev eInvMat : Matrix (Fin 24) (Fin 24) (ZMod 2) := rowsMatrix 24 eInvRows

theorem eMat_mul_eInvMat : eMat * eInvMat = 1 := by
  rw [← rowsMatrix_mulRows, mulRows_e_eInv, rowsMatrix_idRows]

theorem eInvMat_mul_eMat : eInvMat * eMat = 1 := by
  rw [← rowsMatrix_mulRows, mulRows_eInv_e, rowsMatrix_idRows]

noncomputable def vecMulE :
    (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  LinearEquiv.ofLinearMap (Matrix.vecMulLinear eMat) (Matrix.vecMulLinear eInvMat)
    (LinearMap.ext fun u => by
      simp [Matrix.vecMul_vecMul, eInvMat_mul_eMat])
    (LinearMap.ext fun u => by
      simp [Matrix.vecMul_vecMul, eMat_mul_eInvMat])

noncomputable def theta : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] L2 :=
  vecMulE.trans ellBasis.equivFun.symm

theorem theta_toVecD
    (n : ℕ) : theta (toVecD 24 n) = dec (vecMulN 24 eRows n) := by
  rw [dec_eq_ellBasis]
  show ellBasis.equivFun.symm (toVecD 24 n ᵥ* eMat) = _
  rw [← toVecD_vecMulN]
  rfl

theorem toVecD_shiftLeft (i : Fin 24) : toVecD 24 (1 <<< (i : ℕ)) = Pi.single i 1 := by
  funext j
  rw [toVecD_apply, Nat.one_shiftLeft, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : j = i
  · subst h; simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e.symm)
    simp [h, h']

attribute [irreducible] theta

@[expose] noncomputable def u1 : GLV := wordGL xWord

@[expose] noncomputable def u2 : GLV := wordGL yWord

theorem u1_smul_dec
    (v : ℕ) : u1 • dec v = dec (actWord frameMatrices xWord v) :=
  wordGL_smul_dec xWord xWord_lt v

theorem u2_smul_dec
    (v : ℕ) : u2 • dec v = dec (actWord frameMatrices yWord v) :=
  wordGL_smul_dec yWord yWord_lt v

theorem u1_mem_Kvis : u1 ∈ Kvis := wordGL_mem_Kvis xWord xWord_lt

theorem u2_mem_Kvis : u2 ∈ Kvis := wordGL_mem_Kvis yWord yWord_lt

attribute [irreducible] u1 u2

irreducible_def aMat : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  rowsMatrix 24 CFSG.Sporadic.Co1.Native.co1Data.rowsA

irreducible_def bMat : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  rowsMatrix 24 CFSG.Sporadic.Co1.Native.co1Data.rowsB

theorem smul_eq_apply (g : GLV) (v : L2) : g • v = (g : L2 →ₗ[ZMod 2] L2) v := by
  rw [Units.smul_def, Module.End.smul_def]

theorem theta_aMat_single (i : Fin 24) :
    theta (aMat *ᵥ Pi.single i 1) = u1 • theta (Pi.single i 1) := by
  rw [aMat_def, ← toVecD_shiftLeft, rowsMatrix_mulVec, transposeRows_rowsA, theta_toVecD,
    theta_toVecD, u1_smul_dec, xCheck i i.isLt]

theorem theta_bMat_single (i : Fin 24) :
    theta (bMat *ᵥ Pi.single i 1) = u2 • theta (Pi.single i 1) := by
  rw [bMat_def, ← toVecD_shiftLeft, rowsMatrix_mulVec, transposeRows_rowsB, theta_toVecD,
    theta_toVecD, u2_smul_dec, yCheck i i.isLt]

theorem theta_aMat_mulVec
    (u : Fin 24 → ZMod 2) : theta (aMat *ᵥ u) = u1 • theta u := by
  have key : theta.toLinearMap ∘ₗ Matrix.mulVecLin aMat =
      (u1 : L2 →ₗ[ZMod 2] L2) ∘ₗ theta.toLinearMap := by
    refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
    have h := theta_aMat_single i
    rw [smul_eq_apply] at h
    simpa only [LinearMap.comp_apply, LinearMap.coe_single, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe] using h
  rw [smul_eq_apply]
  exact LinearMap.congr_fun key u

theorem theta_bMat_mulVec
    (u : Fin 24 → ZMod 2) : theta (bMat *ᵥ u) = u2 • theta u := by
  have key : theta.toLinearMap ∘ₗ Matrix.mulVecLin bMat =
      (u2 : L2 →ₗ[ZMod 2] L2) ∘ₗ theta.toLinearMap := by
    refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
    have h := theta_bMat_single i
    rw [smul_eq_apply] at h
    simpa only [LinearMap.comp_apply, LinearMap.coe_single, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe] using h
  rw [smul_eq_apply]
  exact LinearMap.congr_fun key u

theorem aMat_mul_self : aMat * aMat = 1 := by
  rw [aMat_def, ← rowsMatrix_mulRows, rowsA_sq, rowsMatrix_idRows]

theorem bMat_pow_three : bMat * (bMat * bMat) = 1 := by
  rw [bMat_def, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, rowsB_cube, rowsMatrix_idRows]

@[expose] noncomputable def gA24 : GL (Fin 24) (ZMod 2) :=
  ⟨aMat, aMat, aMat_mul_self, aMat_mul_self⟩

@[expose] noncomputable def gB24 : GL (Fin 24) (ZMod 2) :=
  ⟨bMat, bMat * bMat, bMat_pow_three, by rw [Matrix.mul_assoc, bMat_pow_three]⟩

noncomputable abbrev J24 :
    Subgroup (GL (Fin 24) (ZMod 2)) := Subgroup.closure {gA24, gB24}

theorem decode_seed1 : Blueprint.NativeSporadic.decode 2 24 1 Blueprint.NativeSporadic.Co1Seed1 =
    aMat := by
  rw [aMat_def, ← rowsMatrix_rowsOfPayload]
  rfl

theorem decode_seed2 : Blueprint.NativeSporadic.decode 2 24 1 Blueprint.NativeSporadic.Co1Seed2 =
    bMat := by
  rw [bMat_def, ← rowsMatrix_rowsOfPayload]
  rfl

theorem seedMonoid_eq : Blueprint.NativeSporadic.seedMonoid 2 24 1
    Blueprint.NativeSporadic.Co1Seed1 Blueprint.NativeSporadic.Co1Seed2 =
      Submonoid.closure ({(gA24 : Matrix (Fin 24) (Fin 24) (ZMod 2)),
        (gB24 : Matrix (Fin 24) (Fin 24) (ZMod 2))} : Set (Matrix (Fin 24) (Fin 24) (ZMod 2))) := by
  rw [Blueprint.NativeSporadic.seedMonoid, decode_seed1, decode_seed2]
  rfl

noncomputable def co1EquivJ24 :
    Blueprint.NativeSporadic.Co1 ≃* J24 :=
  let e₁ : Blueprint.NativeSporadic.Co1 ≃* (Submonoid.closure
      ({(gA24 : Matrix (Fin 24) (Fin 24) (ZMod 2)), (gB24 : Matrix (Fin 24) (Fin 24) (ZMod 2))} :
        Set (Matrix (Fin 24) (Fin 24) (ZMod 2))))ˣ :=
    Units.mapEquiv (MulEquiv.submonoidCongr seedMonoid_eq)
  e₁.trans (Blueprint.NativeSporadic.unitSeedEquiv gA24 gB24)

theorem natCard_J24 :
    Nat.card J24 = 4157776806543360000 := by
  rw [← Nat.card_congr co1EquivJ24.toEquiv]
  exact CFSG.Sporadic.Co1.card_Co1

noncomputable def conjHom : GL (Fin 24) (ZMod 2) →* GLV :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv theta).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

theorem conjHom_injective : Function.Injective conjHom :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv theta).injective.comp
    Matrix.GeneralLinearGroup.toLin.injective

theorem conjHom_apply (g : GL (Fin 24) (ZMod 2)) (v : L2) :
    (conjHom g : L2 →ₗ[ZMod 2] L2) v =
      theta ((g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ theta.symm v) := by
  simp [conjHom, LinearMap.GeneralLinearGroup.congrLinearEquiv_apply,
    Matrix.GeneralLinearGroup.coe_toLin]

theorem conjHom_gA24 : conjHom gA24 = u1 := by
  refine Units.ext (LinearMap.ext fun v => ?_)
  rw [conjHom_apply]
  change theta (aMat *ᵥ theta.symm v) = _
  rw [theta_aMat_mulVec, LinearEquiv.apply_symm_apply, smul_eq_apply]

theorem conjHom_gB24 : conjHom gB24 = u2 := by
  refine Units.ext (LinearMap.ext fun v => ?_)
  rw [conjHom_apply]
  change theta (bMat *ᵥ theta.symm v) = _
  rw [theta_bMat_mulVec, LinearEquiv.apply_symm_apply, smul_eq_apply]

theorem map_J24_eq_closure :
    J24.map conjHom = Subgroup.closure {u1, u2} := by
  rw [MonoidHom.map_closure, Set.image_pair, conjHom_gA24, conjHom_gB24]

theorem closure_le_Kvis : Subgroup.closure {u1, u2} ≤ Kvis := by
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact u1_mem_Kvis
  · exact u2_mem_Kvis

theorem closure_le_Hvis :
    Subgroup.closure {u1, u2} ≤ Hvis := closure_le_Kvis.trans Kvis_le_Hvis

theorem map_J24_eq_Hvis :
    J24.map conjHom = Hvis := by
  refine Subgroup.eq_of_le_of_card_ge (map_J24_eq_closure ▸ closure_le_Hvis) ?_
  rw [natCard_Hvis, Subgroup.card_map_of_injective conjHom_injective, natCard_J24]

theorem closure_eq_Hvis :
    Subgroup.closure {u1, u2} = Hvis :=
  map_J24_eq_closure ▸ map_J24_eq_Hvis

theorem Kvis_eq_Hvis :
    Kvis = Hvis :=
  le_antisymm Kvis_le_Hvis (closure_eq_Hvis ▸ closure_le_Kvis)

noncomputable def jEquivHvis :
    J24 ≃* Hvis :=
  (J24.equivMapOfInjective conjHom conjHom_injective).trans (MulEquiv.subgroupCongr map_J24_eq_Hvis)

noncomputable def co1EquivHvis :
    Blueprint.NativeSporadic.Co1 ≃* Hvis :=
  co1EquivJ24.trans jEquivHvis

noncomputable def visQuotEquivCo1 :
    Gvis ⧸ rhoQ.subgroupOf Gvis ≃* Blueprint.NativeSporadic.Co1 :=
  visQuotEquivHvis.trans co1EquivHvis.symm

theorem full_lattice_quotient_catalog_Co1_isomorphism :
    Subgroup.closure {u1, u2} = Hvis ∧ Kvis = Hvis ∧
      conjHom gA24 = u1 ∧ conjHom gB24 = u2 ∧ J24.map conjHom = Hvis ∧
      Nonempty (Blueprint.NativeSporadic.Co1 ≃* Hvis) ∧
      Nonempty (Gvis ⧸ rhoQ.subgroupOf Gvis ≃* Blueprint.NativeSporadic.Co1) :=
  ⟨closure_eq_Hvis, Kvis_eq_Hvis, conjHom_gA24, conjHom_gB24, map_J24_eq_Hvis,
    ⟨co1EquivHvis⟩, ⟨visQuotEquivCo1⟩⟩

end CFSG.Monster.Existence.Co1Bridge
