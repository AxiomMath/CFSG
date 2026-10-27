module

public import CFSG.Monster.B.Co2CatalogBridge
public import CFSG.Monster.B.Co2.Simple
public import CFSG.Sporadic.Co2Cert.Order
public import CFSG.Monster.B.Gen.Max2AssemblyBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2Catalog

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.VisQuot CFSG.Monster.B CFSG.Monster.B.Short
  CFSG.Monster.B.Co2 CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2Cert
  Matrix

attribute [local irreducible] CFSG.Monster.B.Co2.Native.genRecords

noncomputable abbrev kvM (k : Kstab v0) : Matrix (Fin 22) (Fin 22) (ZMod 2) := kvMat qbWBasis k

theorem quotRows_eq (i : Fin 24) : quotRows i = genQuotMatrix i := rfl

theorem repr_decW (c : ℕ) (s : Fin 22) :
    qbWBasis.repr (decW c) s = toVecD 22 c s := by
  rw [decW_eq_equivFun, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem kvM_alpha
    (i : Fin 24) :
    kvM ⟨alpha i, alpha_mem_Kv i⟩ = rowsMatrix 22 (quotRows i) := by
  ext t s
  have hs : (t : ℕ) < (quotRows i).size := by
    rw [(bridge_check.2.2.2.2.2.2.2.1 i i.2).1]
    exact t.2
  rw [kvM, kvMat_apply, qbWBasis_apply, wAct_alpha_qbW, repr_decW, rowsMatrix_apply,
    Array.getElem?_eq_getElem hs, Option.getD_some, ← getElem!_pos (quotRows i) (t : ℕ) hs]
  rfl

theorem kvM_inv
    (k : Kstab v0) : kvM k⁻¹ * kvM k = 1 := by
  rw [kvM, kvM, ← kvMat_mul, inv_mul_cancel, kvMat_one]

theorem kvM_alpha_inv
    (i : Fin 24) :
    kvM ⟨alpha i, alpha_mem_Kv i⟩⁻¹ =
      rowsMatrix 22 (CFSG.Monster.B.Max2.Native.inv22 (quotRows i)) := by
  have hr : rowsMatrix 22 (quotRows i) *
      rowsMatrix 22 (CFSG.Monster.B.Max2.Native.inv22 (quotRows i)) = 1 := by
    have h := congrArg (rowsMatrix 22) (bridge_check.2.2.2.2.2.2.2.1 i i.2).2
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at h
  have hl := kvM_inv ⟨alpha i, alpha_mem_Kv i⟩
  rw [kvM_alpha] at hl
  calc kvM ⟨alpha i, alpha_mem_Kv i⟩⁻¹
      = kvM ⟨alpha i, alpha_mem_Kv i⟩⁻¹ * (rowsMatrix 22 (quotRows i) *
          rowsMatrix 22 (CFSG.Monster.B.Max2.Native.inv22 (quotRows i))) := by rw [hr, mul_one]
    _ = _ := by rw [← mul_assoc, hl, one_mul]

theorem kvM_letter
    {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 24) :
    kvM ⟨alphaLetter l, alphaLetter_mem l⟩ = rowsMatrix 22 (bridgeLetterRows l) := by
  have hi : l.natAbs - 1 < 24 := by omega
  have hN : (⟨alphaN (l.natAbs - 1), alphaN_mem _⟩ : Kstab v0) =
      ⟨alpha ⟨l.natAbs - 1, hi⟩, alpha_mem_Kv _⟩ := Subtype.ext (by simp [alphaN, hi])
  by_cases hpos : 0 < l
  · have e : (⟨alphaLetter l, alphaLetter_mem l⟩ : Kstab v0) =
        ⟨alphaN (l.natAbs - 1), alphaN_mem _⟩ := Subtype.ext (by simp [alphaLetter, hpos])
    rw [e, hN, kvM_alpha, bridgeLetterRows, ite_eq_left hpos]
  · have e : (⟨alphaLetter l, alphaLetter_mem l⟩ : Kstab v0) =
        (⟨alphaN (l.natAbs - 1), alphaN_mem _⟩ : Kstab v0)⁻¹ :=
      Subtype.ext (by simp [alphaLetter, hpos])
    rw [e, hN, kvM_alpha_inv, bridgeLetterRows, ite_eq_right hpos]

theorem kvM_word :
    ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 24) →
    kvM ⟨alphaWord w, alphaWord_mem w⟩ = rowsMatrix 22 (bridgeWordRows w)
  | [], _ => by
    have e : (⟨alphaWord [], alphaWord_mem []⟩ : Kstab v0) = 1 := rfl
    rw [e, kvM, kvMat_one, bridgeWordRows, rowsMatrix_idRows]
  | l :: w, hw => by
    have e : (⟨alphaWord (l :: w), alphaWord_mem (l :: w)⟩ : Kstab v0) =
        ⟨alphaLetter l, alphaLetter_mem l⟩ * ⟨alphaWord w, alphaWord_mem w⟩ := rfl
    rw [e, kvM, kvMat_mul, ← kvM, ← kvM, kvM_letter (hw l List.mem_cons_self),
      kvM_word w fun l' h => hw l' (List.mem_cons_of_mem _ h), bridgeWordRows,
      rowsMatrix_mulRows]

theorem kvM_U1 :
    kvM ⟨bridgeU1, bridgeU1_mem⟩ = bridgeNativeMat 0 := by
  have hw : ∀ l ∈ bridgeRec.nativeAWord, l ≠ 0 ∧ l.natAbs ≤ 24 := by
    rw [bridge_check.1]
    decide
  rw [show (⟨bridgeU1, bridgeU1_mem⟩ : Kstab v0) =
      ⟨alphaWord bridgeRec.nativeAWord, alphaWord_mem _⟩ from rfl, kvM_word _ hw,
    bridge_check.2.2.2.2.2.2.2.2.1, bridgeNativeMat]

theorem kvM_U2 :
    kvM ⟨bridgeU2, bridgeU2_mem⟩ = bridgeNativeMat 1 := by
  rw [show (⟨bridgeU2, bridgeU2_mem⟩ : Kstab v0) =
      ⟨alphaWord bridgeRec.nativeBWord, alphaWord_mem _⟩ from rfl,
    kvM_word _ bridge_check.2.2.1, bridge_check.2.2.2.2.2.2.2.2.2.1, bridgeNativeMat]

theorem catalogRows_zero : rowsMatrix 22 (catalogRows 0) = co2A1 := by
  rw [catalogRows, ite_eq_left rfl, rowsMatrix_rowsOfPayload, co2SeedA_eq]

theorem catalogRows_one : rowsMatrix 22 (catalogRows 1) = co2A2 := by
  rw [catalogRows, ite_eq_right one_ne_zero, rowsMatrix_rowsOfPayload, co2SeedB_eq]

theorem co2A1_transpose : co2A1ᵀ = bridgeCatalogMat 0 := by
  rw [bridgeCatalogMat, ← bridge_check.2.2.2.2.2.2.2.2.2.2.1, rowsMatrix_transposeRows,
    catalogRows_zero]

theorem co2A2_transpose : co2A2ᵀ = bridgeCatalogMat 1 := by
  rw [bridgeCatalogMat, ← bridge_check.2.2.2.2.2.2.2.2.2.2.2.1, rowsMatrix_transposeRows,
    catalogRows_one]

theorem bridgeC_mul_inv :
    bridgeC * rowsMatrix 22 (CFSG.Monster.B.Max2.Native.inv22 bridgeCRows) = 1 := by
  have h := congrArg (rowsMatrix 22) bridge_check.2.2.2.2.2.2.2.2.2.2.2.2.1
  rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at h

theorem isUnit_bridgeC :
    IsUnit bridgeC := IsUnit.of_mul_eq_one _ bridgeC_mul_inv

theorem det_bridgeC_ne_zero : bridgeC.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 isUnit_bridgeC).ne_zero

theorem kvM_U1_mul_C :
    kvM ⟨bridgeU1, bridgeU1_mem⟩ * bridgeC = bridgeC * co2A1ᵀ := by
  have h := congrArg (rowsMatrix 22) bridge_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows] at h
  rw [kvM_U1, co2A1_transpose]
  exact h

theorem kvM_U2_mul_C :
    kvM ⟨bridgeU2, bridgeU2_mem⟩ * bridgeC = bridgeC * co2A2ᵀ := by
  have h := congrArg (rowsMatrix 22) bridge_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows] at h
  rw [kvM_U2, co2A2_transpose]
  exact h

@[expose] noncomputable def glInvTranspose : GL (Fin 22) (ZMod 2) →* GL (Fin 22) (ZMod 2) where
  toFun A := ⟨((A⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2))ᵀ,
    (A : Matrix (Fin 22) (Fin 22) (ZMod 2))ᵀ,
    by rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one],
    by rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' A B := Units.ext (by
    change (((A * B)⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2))ᵀ =
      ((A⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2))ᵀ *
        ((B⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2))ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul])

theorem coe_glInvTranspose (A : GL (Fin 22) (ZMod 2)) :
    (glInvTranspose A : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      ((A : Matrix (Fin 22) (Fin 22) (ZMod 2))⁻¹)ᵀ := by
  change ((A⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2))ᵀ = _
  rw [Matrix.coe_units_inv]

theorem glInvTranspose_injective : Function.Injective glInvTranspose := by
  intro A B h
  have h1 : ((A⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2))ᵀ =
      ((B⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2))ᵀ :=
    congrArg Units.val h
  exact inv_injective (Units.ext (Matrix.transpose_injective h1))

@[expose] noncomputable def bridgeCGL : GL (Fin 22) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero bridgeC det_bridgeC_ne_zero

@[expose] noncomputable def phiHom :
    Kstab v0 →* GL (Fin 22) (ZMod 2) :=
  glInvTranspose.comp ((MulAut.conj bridgeCGL⁻¹).toMonoidHom.comp (kvGL qbWBasis))

theorem coe_phiHom
    (k : Kstab v0) :
    (phiHom k : Matrix (Fin 22) (Fin 22) (ZMod 2)) = ((bridgeC⁻¹ * kvM k * bridgeC)⁻¹)ᵀ := by
  rw [phiHom, MonoidHom.comp_apply, coe_glInvTranspose, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Units.val_mul, Units.val_mul,
    Matrix.coe_units_inv, coe_kvGL]
  rfl

theorem phiHom_injective :
    Function.Injective phiHom :=
  glInvTranspose_injective.comp ((MulAut.conj bridgeCGL⁻¹).injective.comp
    (kvGL_injective KvAct_injective_vMinus qbWBasis))

theorem bridgeC_inv_mul
    (M D : Matrix (Fin 22) (Fin 22) (ZMod 2)) (h : M * bridgeC = bridgeC * D) :
    bridgeC⁻¹ * M * bridgeC = D := by
  rw [mul_assoc, h, ← mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1
    isUnit_bridgeC), one_mul]

theorem phiHom_U1 :
    phiHom ⟨bridgeU1, bridgeU1_mem⟩ = co2GL1⁻¹ := by
  apply Units.ext
  rw [coe_phiHom, bridgeC_inv_mul _ _ kvM_U1_mul_C, ← Matrix.transpose_nonsing_inv,
    transpose_transpose, Matrix.coe_units_inv]
  rfl

theorem phiHom_U2 :
    phiHom ⟨bridgeU2, bridgeU2_mem⟩ = co2GL2⁻¹ := by
  apply Units.ext
  rw [coe_phiHom, bridgeC_inv_mul _ _ kvM_U2_mul_C, ← Matrix.transpose_nonsing_inv,
    transpose_transpose, Matrix.coe_units_inv]
  rfl

noncomputable abbrev uGrp :
    Subgroup (Kstab v0) :=
  Subgroup.closure {⟨bridgeU1, bridgeU1_mem⟩, ⟨bridgeU2, bridgeU2_mem⟩}

theorem closure_inv_pair {G : Type*} [Group G] (a b : G) :
    Subgroup.closure ({a⁻¹, b⁻¹} : Set G) = Subgroup.closure {a, b} := by
  rw [← Set.inv_singleton, ← Set.inv_insert, Subgroup.closure_inv]

theorem uGrp_map :
    uGrp.map phiHom = co2J := by
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, phiHom_U1, phiHom_U2,
    closure_inv_pair]

theorem natCard_co2J :
    Nat.card co2J = 42305421312000 := by
  rw [← Nat.card_congr co2MatEquiv.toEquiv]
  exact natCard_Co2

theorem uGrp_eq_top :
    uGrp = ⊤ := by
  refine Subgroup.eq_top_of_le_card _ (le_of_eq ?_)
  rw [natCard_Kv, ← natCard_co2J, ← uGrp_map, Subgroup.card_map_of_injective phiHom_injective]

theorem closure_U_eq_Kv :
    Subgroup.closure {bridgeU1, bridgeU2} = Kstab v0 := by
  have h := congrArg (Subgroup.map (Kstab v0).subtype) uGrp_eq_top
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  rw [← h, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem phiHom_range :
    phiHom.range = co2J := by
  rw [MonoidHom.range_eq_map, ← uGrp_eq_top, uGrp_map]

@[expose] noncomputable def kvEquivJ :
    Kstab v0 ≃* co2J :=
  (MonoidHom.ofInjective phiHom_injective).trans (MulEquiv.subgroupCongr phiHom_range)

theorem kvEquivJ_val
    (k : Kstab v0) :
    ((kvEquivJ k : co2J) : GL (Fin 22) (ZMod 2)) = phiHom k := rfl

@[expose] noncomputable def co2CatalogEquiv :
    Kstab v0 ≃* Blueprint.NativeSporadic.Co2 :=
  kvEquivJ.trans co2MatEquiv.symm

theorem co2CatalogEquiv_val
    (k : Kstab v0) :
    (co2CatalogEquiv k).val.val = ((bridgeC⁻¹ * kvM k * bridgeC)⁻¹)ᵀ := by
  rw [← co2MatEquiv_val, co2CatalogEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    kvEquivJ_val, coe_phiHom]

theorem kvEquivJ_U1 :
    kvEquivJ ⟨bridgeU1, bridgeU1_mem⟩ =
    (⟨co2GL1, Subgroup.subset_closure (Set.mem_insert _ _)⟩ : co2J)⁻¹ := by
  apply Subtype.ext
  rw [kvEquivJ_val, phiHom_U1, Subgroup.coe_inv]

theorem kvEquivJ_U2 :
    kvEquivJ ⟨bridgeU2, bridgeU2_mem⟩ =
    (⟨co2GL2, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩ : co2J)⁻¹ := by
  apply Subtype.ext
  rw [kvEquivJ_val, phiHom_U2, Subgroup.coe_inv]

theorem co2CatalogEquiv_U1 :
    co2CatalogEquiv ⟨bridgeU1, bridgeU1_mem⟩ = co2SeedA⁻¹ := by
  rw [co2CatalogEquiv, MulEquiv.trans_apply, kvEquivJ_U1, map_inv]
  rfl

theorem co2CatalogEquiv_U2 :
    co2CatalogEquiv ⟨bridgeU2, bridgeU2_mem⟩ = co2SeedB⁻¹ := by
  rw [co2CatalogEquiv, MulEquiv.trans_apply, kvEquivJ_U2, map_inv]
  rfl

theorem co2CatalogEquiv_U1_val :
    (co2CatalogEquiv ⟨bridgeU1, bridgeU1_mem⟩).val.val = co2A1⁻¹ := by
  rw [co2CatalogEquiv_val, bridgeC_inv_mul _ _ kvM_U1_mul_C, ← Matrix.transpose_nonsing_inv,
    transpose_transpose]

theorem co2CatalogEquiv_U2_val :
    (co2CatalogEquiv ⟨bridgeU2, bridgeU2_mem⟩).val.val = co2A2⁻¹ := by
  rw [co2CatalogEquiv_val, bridgeC_inv_mul _ _ kvM_U2_mul_C, ← Matrix.transpose_nonsing_inv,
    transpose_transpose]

theorem nonempty_kstab_co2
    {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    Nonempty (Kstab (classOf u) ≃* Blueprint.NativeSporadic.Co2) := by
  obtain ⟨e⟩ := nonempty_kstabEquiv hu
  exact ⟨e.trans co2CatalogEquiv⟩

@[expose] noncomputable def jbarQuotEquiv :
    Jbar ⧸ Ebar.subgroupOf Jbar ≃* Blueprint.NativeSporadic.Co2 :=
  (QuotientGroup.quotientMulEquivOfEq ker_jbarToKv.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective jbarToKv jbarToKv_surjective).trans
      ((MulEquiv.subgroupCongr (congrArg Kstab phi0_coordOf_rStar)).trans co2CatalogEquiv))

theorem mon_native_short_stabilizer_catalog_co2_isomorphism :
    IsUnit bridgeC ∧
    kvM ⟨bridgeU1, bridgeU1_mem⟩ * bridgeC = bridgeC * co2A1ᵀ ∧
    kvM ⟨bridgeU2, bridgeU2_mem⟩ * bridgeC = bridgeC * co2A2ᵀ ∧
    kvM ⟨bridgeU1, bridgeU1_mem⟩ = bridgeNativeMat 0 ∧
    kvM ⟨bridgeU2, bridgeU2_mem⟩ = bridgeNativeMat 1 ∧
    co2A1ᵀ = bridgeCatalogMat 0 ∧ co2A2ᵀ = bridgeCatalogMat 1 ∧
    Subgroup.closure {bridgeU1, bridgeU2} = Kstab v0 ∧
    (∀ k : Kstab v0, (co2CatalogEquiv k).val.val = ((bridgeC⁻¹ * kvM k * bridgeC)⁻¹)ᵀ) ∧
    co2CatalogEquiv ⟨bridgeU1, bridgeU1_mem⟩ = co2SeedA⁻¹ ∧
    co2CatalogEquiv ⟨bridgeU2, bridgeU2_mem⟩ = co2SeedB⁻¹ ∧
    (co2CatalogEquiv ⟨bridgeU1, bridgeU1_mem⟩).val.val = co2A1⁻¹ ∧
    (co2CatalogEquiv ⟨bridgeU2, bridgeU2_mem⟩).val.val = co2A2⁻¹ ∧
    co2SeedA.val.val = co2A1 ∧ co2SeedB.val.val = co2A2 ∧
    (∀ u ∈ minVecs, Nonempty (Kstab (classOf u) ≃* Blueprint.NativeSporadic.Co2)) ∧
    Nonempty (Jbar ⧸ Ebar.subgroupOf Jbar ≃* Blueprint.NativeSporadic.Co2) :=
  ⟨isUnit_bridgeC, kvM_U1_mul_C, kvM_U2_mul_C, kvM_U1, kvM_U2, co2A1_transpose, co2A2_transpose,
    closure_U_eq_Kv, co2CatalogEquiv_val, co2CatalogEquiv_U1, co2CatalogEquiv_U2,
    co2CatalogEquiv_U1_val, co2CatalogEquiv_U2_val, co2SeedA_val, co2SeedB_val,
    fun _ hu => nonempty_kstab_co2 hu, ⟨jbarQuotEquiv⟩⟩

end CFSG.Monster.B.Co2Catalog
