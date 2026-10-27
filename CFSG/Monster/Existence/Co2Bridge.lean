module

public import CFSG.Monster.Existence.Co2BridgeData
public import CFSG.Monster.B.Co2.Simple
public import CFSG.Sporadic.Co2
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.Co2Bridge

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Short CFSG.Monster.B.Co2
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

noncomputable abbrev eMat : Matrix (Fin 22) (Fin 22) (ZMod 2) := rowsMatrix 22 eRows

noncomputable abbrev eInvMat : Matrix (Fin 22) (Fin 22) (ZMod 2) := rowsMatrix 22 eInvRows

theorem eMat_mul_eInvMat : eMat * eInvMat = 1 := by
  rw [← rowsMatrix_mulRows, mulRows_e_eInv, rowsMatrix_idRows]

theorem eInvMat_mul_eMat : eInvMat * eMat = 1 := by
  rw [← rowsMatrix_mulRows, mulRows_eInv_e, rowsMatrix_idRows]

noncomputable def vecMulE :
    (Fin 22 → ZMod 2) ≃ₗ[ZMod 2] (Fin 22 → ZMod 2) :=
  LinearEquiv.ofLinearMap (Matrix.vecMulLinear eMat) (Matrix.vecMulLinear eInvMat)
    (LinearMap.ext fun u => by
      simp [Matrix.vecMul_vecMul, eInvMat_mul_eMat])
    (LinearMap.ext fun u => by
      simp [Matrix.vecMul_vecMul, eMat_mul_eInvMat])

noncomputable def theta :
    (Fin 22 → ZMod 2) ≃ₗ[ZMod 2] Wv v0 :=
  vecMulE.trans qbWBasis.equivFun.symm

theorem theta_toVecD
    (n : ℕ) : theta (toVecD 22 n) = decW (vecMulN 22 eRows n) := by
  rw [decW_eq_equivFun]
  show qbWBasis.equivFun.symm (toVecD 22 n ᵥ* eMat) = _
  rw [← toVecD_vecMulN]
  rfl

theorem toVecD_shiftLeft (i : Fin 22) : toVecD 22 (1 <<< (i : ℕ)) = Pi.single i 1 := by
  funext j
  rw [toVecD_apply, Nat.one_shiftLeft, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : j = i
  · subst h; simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e.symm)
    simp [h, h']

attribute [irreducible] theta

@[expose] noncomputable def alphaK
    (l : ℕ) : Kstab v0 :=
  if h : l < 24 then ⟨alpha ⟨l, h⟩, alpha_mem_Kv _⟩ else 1

@[expose] noncomputable def wordK
    (w : List ℕ) : Kstab v0 := (w.map alphaK).prod

theorem wAct_alphaK_decW
    {l : ℕ} (hl : l < 24) (c : ℕ) :
    wAct v0 (alphaK l) (decW c) = decW (CFSG.Monster.B.Co2.Native.actD 22 (qMat l) c) := by
  have h : alphaK l = ⟨alpha ⟨l, hl⟩, alpha_mem_Kv _⟩ := by simp [alphaK, hl]
  rw [h]
  exact wAct_alpha_decW ⟨l, hl⟩ c

theorem wAct_wordK_decW
    (w : List ℕ) (hw : ∀ l ∈ w, l < 24) (c : ℕ) :
    wAct v0 (wordK w) (decW c) = decW (actWordQ w c) := by
  induction w generalizing c with
  | nil =>
    rw [wordK, List.map_nil, List.prod_nil, wAct_one, Module.End.one_apply]
    rfl
  | cons l w ih =>
    rw [wordK, List.map_cons, List.prod_cons, wAct_mul, Module.End.mul_apply,
      wAct_alphaK_decW (hw l (by simp)) c]
    exact ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _

@[expose] noncomputable def xK :
    Kstab v0 := wordK xWord

@[expose] noncomputable def yK :
    Kstab v0 := wordK yWord

theorem wAct_xK_decW
    (c : ℕ) : wAct v0 xK (decW c) = decW (actWordQ xWord c) :=
  wAct_wordK_decW xWord xWord_lt c

theorem wAct_yK_decW
    (c : ℕ) : wAct v0 yK (decW c) = decW (actWordQ yWord c) :=
  wAct_wordK_decW yWord yWord_lt c

attribute [irreducible] xK yK

irreducible_def aMat : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  rowsMatrix 22 CFSG.Sporadic.Co2.Native.co2Data.rowsA

irreducible_def bMat : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  rowsMatrix 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB

theorem theta_aMat_single
    (i : Fin 22) :
    theta (aMat *ᵥ Pi.single i 1) = wAct v0 xK (theta (Pi.single i 1)) := by
  rw [aMat_def, ← toVecD_shiftLeft, rowsMatrix_mulVec, transposeRows_rowsA, theta_toVecD,
    theta_toVecD, wAct_xK_decW, xCheck i i.isLt]

theorem theta_bMat_single
    (i : Fin 22) :
    theta (bMat *ᵥ Pi.single i 1) = wAct v0 yK (theta (Pi.single i 1)) := by
  rw [bMat_def, ← toVecD_shiftLeft, rowsMatrix_mulVec, transposeRows_rowsB, theta_toVecD,
    theta_toVecD, wAct_yK_decW, yCheck i i.isLt]

theorem theta_aMat_mulVec
    (u : Fin 22 → ZMod 2) : theta (aMat *ᵥ u) = wAct v0 xK (theta u) := by
  have key : theta.toLinearMap ∘ₗ Matrix.mulVecLin aMat = wAct v0 xK ∘ₗ theta.toLinearMap := by
    refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
    simpa only [LinearMap.comp_apply, LinearMap.coe_single, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe] using theta_aMat_single i
  exact LinearMap.congr_fun key u

theorem theta_bMat_mulVec
    (u : Fin 22 → ZMod 2) : theta (bMat *ᵥ u) = wAct v0 yK (theta u) := by
  have key : theta.toLinearMap ∘ₗ Matrix.mulVecLin bMat = wAct v0 yK ∘ₗ theta.toLinearMap := by
    refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
    simpa only [LinearMap.comp_apply, LinearMap.coe_single, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe] using theta_bMat_single i
  exact LinearMap.congr_fun key u

theorem aMat_mul_self : aMat * aMat = 1 := by
  rw [aMat_def, ← rowsMatrix_mulRows, rowsA_sq, rowsMatrix_idRows]

theorem bMat_pow_five :
    bMat * (bMat * (bMat * (bMat * bMat))) = 1 := by
  rw [bMat_def, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows,
    ← rowsMatrix_mulRows, rowsB_pow_five, rowsMatrix_idRows]

@[expose] noncomputable def gA22 : GL (Fin 22) (ZMod 2) :=
  ⟨aMat, aMat, aMat_mul_self, aMat_mul_self⟩

@[expose] noncomputable def gB22 : GL (Fin 22) (ZMod 2) :=
  ⟨bMat, bMat * (bMat * (bMat * bMat)), bMat_pow_five, by
    simp only [Matrix.mul_assoc]
    exact bMat_pow_five⟩

noncomputable abbrev J22 :
    Subgroup (GL (Fin 22) (ZMod 2)) := Subgroup.closure {gA22, gB22}

theorem decode_seed1 : Blueprint.NativeSporadic.decode 2 22 1 Blueprint.NativeSporadic.Co2Seed1 =
    aMat := by
  rw [aMat_def, ← rowsMatrix_rowsOfPayload]
  rfl

theorem decode_seed2 : Blueprint.NativeSporadic.decode 2 22 1 Blueprint.NativeSporadic.Co2Seed2 =
    bMat := by
  rw [bMat_def, ← rowsMatrix_rowsOfPayload]
  rfl

theorem seedMonoid_eq : Blueprint.NativeSporadic.seedMonoid 2 22 1
    Blueprint.NativeSporadic.Co2Seed1 Blueprint.NativeSporadic.Co2Seed2 =
      Submonoid.closure ({(gA22 : Matrix (Fin 22) (Fin 22) (ZMod 2)),
        (gB22 : Matrix (Fin 22) (Fin 22) (ZMod 2))} : Set (Matrix (Fin 22) (Fin 22) (ZMod 2))) := by
  rw [Blueprint.NativeSporadic.seedMonoid, decode_seed1, decode_seed2]
  rfl

noncomputable def co2EquivJ22 :
    Blueprint.NativeSporadic.Co2 ≃* J22 :=
  let e₁ : Blueprint.NativeSporadic.Co2 ≃* (Submonoid.closure
      ({(gA22 : Matrix (Fin 22) (Fin 22) (ZMod 2)), (gB22 : Matrix (Fin 22) (Fin 22) (ZMod 2))} :
        Set (Matrix (Fin 22) (Fin 22) (ZMod 2))))ˣ :=
    Units.mapEquiv (MulEquiv.submonoidCongr seedMonoid_eq)
  e₁.trans (Blueprint.NativeSporadic.unitSeedEquiv gA22 gB22)

theorem natCard_J22 :
    Nat.card J22 = 42305421312000 := by
  rw [← Nat.card_congr co2EquivJ22.toEquiv]
  exact CFSG.Sporadic.Co2.card_Co2

@[expose] noncomputable def wActHom : Kstab v0 →* LinearMap.GeneralLinearGroup (ZMod 2) (Wv v0) where
  toFun k := ⟨wAct v0 k⁻¹, wAct v0 k, by rw [← wAct_mul, mul_inv_cancel, wAct_one],
    by rw [← wAct_mul, inv_mul_cancel, wAct_one]⟩
  map_one' := Units.ext (by
    change wAct v0 1⁻¹ = 1
    rw [inv_one, wAct_one])
  map_mul' k k' := Units.ext (by
    change wAct v0 (k * k')⁻¹ = wAct v0 k⁻¹ * wAct v0 k'⁻¹
    rw [_root_.mul_inv_rev, wAct_mul])

theorem wActHom_apply (k : Kstab v0) (w : Wv v0) :
    (wActHom k : Wv v0 →ₗ[ZMod 2] Wv v0) w = wAct v0 k⁻¹ w := rfl

theorem wActHom_injective : Function.Injective wActHom := by
  intro k k' h
  have h1 : wAct v0 k⁻¹ = wAct v0 k'⁻¹ := congrArg Units.val h
  have h2 : KvAct v0 k⁻¹ = KvAct v0 k'⁻¹ := congrArg MulOpposite.op h1
  exact inv_injective (KvAct_injective_vMinus h2)

noncomputable def conjHom :
    GL (Fin 22) (ZMod 2) →* LinearMap.GeneralLinearGroup (ZMod 2) (Wv v0) :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv theta).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

theorem conjHom_injective :
    Function.Injective conjHom :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv theta).injective.comp
    Matrix.GeneralLinearGroup.toLin.injective

theorem conjHom_apply
    (g : GL (Fin 22) (ZMod 2)) (w : Wv v0) :
    (conjHom g : Wv v0 →ₗ[ZMod 2] Wv v0) w =
      theta ((g : Matrix (Fin 22) (Fin 22) (ZMod 2)) *ᵥ theta.symm w) := by
  simp [conjHom, LinearMap.GeneralLinearGroup.congrLinearEquiv_apply,
    Matrix.GeneralLinearGroup.coe_toLin]

theorem conjHom_gA22 :
    conjHom gA22 = wActHom xK⁻¹ := by
  refine Units.ext (LinearMap.ext fun w => ?_)
  rw [conjHom_apply, wActHom_apply, inv_inv]
  change theta (aMat *ᵥ theta.symm w) = _
  rw [theta_aMat_mulVec, LinearEquiv.apply_symm_apply]

theorem conjHom_gB22 :
    conjHom gB22 = wActHom yK⁻¹ := by
  refine Units.ext (LinearMap.ext fun w => ?_)
  rw [conjHom_apply, wActHom_apply, inv_inv]
  change theta (bMat *ᵥ theta.symm w) = _
  rw [theta_bMat_mulVec, LinearEquiv.apply_symm_apply]

theorem map_J22_eq_closure :
    J22.map conjHom = (Subgroup.closure {xK⁻¹, yK⁻¹}).map wActHom := by
  rw [MonoidHom.map_closure, MonoidHom.map_closure, Set.image_pair, Set.image_pair, conjHom_gA22,
    conjHom_gB22]

theorem natCard_closure_inv :
    Nat.card (Subgroup.closure {xK⁻¹, yK⁻¹}) = 42305421312000 := by
  rw [← Subgroup.card_map_of_injective wActHom_injective, ← map_J22_eq_closure,
    Subgroup.card_map_of_injective conjHom_injective, natCard_J22]

theorem closure_inv_eq_top :
    Subgroup.closure {xK⁻¹, yK⁻¹} = ⊤ :=
  Subgroup.eq_top_of_card_eq _ (by rw [natCard_closure_inv, natCard_Kv])

theorem closure_xK_yK :
    Subgroup.closure {xK, yK} = ⊤ := by
  refine eq_top_iff.2 (closure_inv_eq_top ▸ ?_)
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))

theorem map_J22_eq_range :
    J22.map conjHom = wActHom.range := by
  rw [map_J22_eq_closure, closure_inv_eq_top, ← MonoidHom.range_eq_map]

noncomputable def kvEquivJ22 :
    Kstab v0 ≃* J22 :=
  (wActHom.ofInjective wActHom_injective).trans
    ((MulEquiv.subgroupCongr map_J22_eq_range.symm).trans
      (J22.equivMapOfInjective conjHom conjHom_injective).symm)

noncomputable def kvEquivCo2 :
    Kstab v0 ≃* Blueprint.NativeSporadic.Co2 :=
  kvEquivJ22.trans co2EquivJ22.symm

theorem short_stabilizer_Co2_isomorphism :
    conjHom gA22 = wActHom xK⁻¹ ∧ conjHom gB22 = wActHom yK⁻¹ ∧
      J22.map conjHom = wActHom.range ∧ Subgroup.closure {xK, yK} = ⊤ ∧
      Nonempty (Kstab v0 ≃* Blueprint.NativeSporadic.Co2) :=
  ⟨conjHom_gA22, conjHom_gB22, map_J22_eq_range, closure_xK_yK, ⟨kvEquivCo2⟩⟩

end CFSG.Monster.Existence.Co2Bridge
