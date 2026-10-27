module

public import CFSG.Sporadic.Schreier.PairMcLCert
public import CFSG.Sporadic.Schreier.PairAction
public import CFSG.Sporadic.McL.Setup
public import CFSG.F3.SepSpec
public import CFSG.Blueprint.MatrixSeedIdentification
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public meta import CFSG.Sporadic.Schreier.PairMcLCert
public meta import Certificates.Data.CFSGNative.J1.Vec
public meta import Certificates.Data.CFSGNative.F3.Sep
public meta import Certificates.Data.CFSGNative.McL.Certificate
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate2240
public import CFSG.Sporadic.Schreier.PairMcLFaithfulInputs
public import Certificates.Certificate2244
public import Certificates.Certificate3170

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.J1 CFSG.Sporadic.J1.Native Matrix
  CFSG.F3.Native

theorem mcl_faithful_check :
    mclFaithfulWith mclVectors mclStrongArrs CFSG.Sporadic.McL.Native.matA
      CFSG.Sporadic.McL.Native.matB = true :=
  Certificates.certificate2244

@[expose] def mclBasisMat : List (List ℕ) := mclBasisMatWith mclVectors

@[expose] def mclBasisInv : List (List ℕ) := gaussInv 3 21 mclBasisMat

theorem mcl_faithful_parts :
    (∀ i < 275, mclVectors[i]!.any (· != 0) = true) ∧
    (∀ i < 275, ∀ j < i, mclVectors[i]! ≠ mclVectors[j]!) ∧
    (∀ i < 275, (mulVecM 21 CFSG.Sporadic.McL.Native.matA (vOfList 21 mclVectors[i]!)).beq
      (vOfList 21 mclVectors[(mclStrongArrs[0]!)[i]!]!) = true) ∧
    (∀ i < 275, (mulVecM 21 CFSG.Sporadic.McL.Native.matB (vOfList 21 mclVectors[i]!)).beq
      (vOfList 21 mclVectors[(mclStrongArrs[1]!)[i]!]!) = true) ∧
    CFSG.Sporadic.J1.Native.wfM 21 mclBasisInv = true ∧
    mulL 3 21 mclBasisInv mclBasisMat = idL 21 := by
  have h := mcl_faithful_check
  unfold mclFaithfulWith at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun i hi => allLt_spec h1 hi, fun i hi j hj => ?_, fun i hi => ?_, fun i hi => ?_, h4,
    h5⟩
  · have := allLt_spec (allLt_spec h2 hi) hj
    simpa using this
  · have := allLt_spec h3 hi
    simp only [Bool.and_eq_true] at this
    exact this.1
  · have := allLt_spec h3 hi
    simp only [Bool.and_eq_true] at this
    exact this.2

theorem mclVectors_wfV {i : ℕ} (hi : i < 275) : wfV 3 21 mclVectors[i]! = true :=
  mclCertOK_parts.2.1 i hi

theorem mclVectors_length {i : ℕ} (hi : i < 275) : mclVectors[i]!.length = 21 :=
  (wfV_iff.1 (mclVectors_wfV hi)).1

theorem mclVec_ne_zero {i : ℕ} (hi : i < 275) : mclVec i ≠ 0 := by
  have h := mcl_faithful_parts.1 i hi
  obtain ⟨x, hx, hx0⟩ := List.any_eq_true.1 h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have hk21 : k < 21 := by rw [← mclVectors_length hi]; exact hk
  intro h0
  have h1 := congrFun h0 ⟨k, hk21⟩
  have hlt := (wfV_iff.1 (mclVectors_wfV hi)).2 _ (List.getElem_mem hk)
  simp only [mclVec, toV, Pi.zero_apply] at h1
  rw [List.getD_eq_getElem _ _ hk] at h1
  have h2 := congrArg ZMod.val h1
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ZMod.val_zero] at h2
  simp [h2] at hx0

theorem mclVec_inj {i j : ℕ} (hi : i < 275) (hj : j < 275) (h : mclVec i = mclVec j) : i = j := by
  have he := toV_inj (mclVectors_wfV hi) (mclVectors_wfV hj) h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact mcl_faithful_parts.2.1 j hj i hlt he.symm
  · exact mcl_faithful_parts.2.1 i hi j hlt he

theorem vOfList_wf (d : ℕ) (v : List ℕ) : (vOfList d v).wf = true := V.wf_ofFn d _

theorem vecOf_vOfList {v : List ℕ} : vecOf 21 (vOfList 21 v) = toV 3 21 v := by
  funext j
  rw [vecOf, vOfList, V.val_ofFn, ite_eq_left j.2]
  rfl

theorem mclVec_eq (i : ℕ) : mclVec i = vecOf 21 (vOfList 21 mclVectors[i]!) := by
  rw [vecOf_vOfList]
  rfl

theorem mclStrongArrs_get_lt {k : ℕ} (hk : k < 13) {i : ℕ} (hi : i < 275) :
    (mclStrongArrs[k]!)[i]! < 275 := by
  have := rep_mclStrongPerm hk ⟨i, hi⟩
  rw [show (mclStrongArrs[k]!)[i]! = (mclStrongArrs[k]!)[((⟨i, hi⟩ : Fin 275) : ℕ)]! from rfl,
    this]
  exact Fin.isLt _

theorem mcl_mulVec {M : Array V} {i j : ℕ}
    (h : (mulVecM 21 M (vOfList 21 mclVectors[i]!)).beq (vOfList 21 mclVectors[j]!) = true) :
    toMat 21 M *ᵥ mclVec i = mclVec j := by
  rw [mclVec_eq i, mclVec_eq j, ← vecOf_mulVecM M (vOfList_wf 21 _)]
  funext r
  exact V.val_ext h r

theorem mclA1_mulVec {i : ℕ} (hi : i < 275) :
    CFSG.Sporadic.McL.mA *ᵥ mclVec i = mclVec (mclStrongArrs[0]!)[i]! := by
  rw [← CFSG.Sporadic.McL.toMat_matA]
  exact mcl_mulVec (mcl_faithful_parts.2.2.1 i hi)

theorem mclA2_mulVec {i : ℕ} (hi : i < 275) :
    CFSG.Sporadic.McL.mB *ᵥ mclVec i = mclVec (mclStrongArrs[1]!)[i]! := by
  rw [← CFSG.Sporadic.McL.toMat_matB]
  exact mcl_mulVec (mcl_faithful_parts.2.2.2.1 i hi)

theorem rep_mclGen {k : ℕ} (hk : k < 13) : Rep 275 mclStrongArrs[k]! (mclGen k) :=
  rep_mclStrongPerm hk

theorem mcl_seed_mulVec (i : Fin 275) :
    CFSG.Sporadic.McL.mA *ᵥ mclVec i = mclVec (mclGen 0 i) ∧
      CFSG.Sporadic.McL.mB *ᵥ mclVec i = mclVec (mclGen 1 i) := by
  refine ⟨?_, ?_⟩
  · rw [mclA1_mulVec i.2, rep_mclGen (by norm_num : 0 < 13) i]
  · rw [mclA2_mulVec i.2, rep_mclGen (by norm_num : 1 < 13) i]

@[expose] def mclC : Matrix (Fin 21) (Fin 21) (ZMod 3) := toM 3 21 mclBasisMat

theorem mclBasisMat_wfM : CFSG.Sporadic.J1.Native.wfM 21 mclBasisMat = true :=
  wfM_colMat (by simp [mclBasisIdx])

theorem mclC_left_inv : toM 3 21 mclBasisInv * mclC = 1 := by
  rw [mclC, ← toM_mulL mcl_faithful_parts.2.2.2.2.1 mclBasisMat_wfM,
    mcl_faithful_parts.2.2.2.2.2, toM_idL]

theorem mclBasisIdx_lt (k : Fin 21) : mclBasisIdx.getD k 0 < 275 := by
  fin_cases k <;> simp [mclBasisIdx]

theorem mclC_col (k : Fin 21) : (fun i => mclC i k) = mclVec (mclBasisIdx.getD k 0) := by
  funext i
  rw [mclC, mclBasisMat, mclBasisMatWith, toM_colMat_apply _ i k (by simp [mclBasisIdx])]
  rw [List.getD_eq_getElem _ _ (by simp [mclBasisIdx]), List.getElem_map,
    List.getD_eq_getElem _ _ (by simp [mclBasisIdx])]
  rfl

theorem mclC_mul_inv : mclC * toM 3 21 mclBasisInv = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 mclC_left_inv

@[expose] def mclCEquiv : (Fin 21 → ZMod 3) ≃ₗ[ZMod 3] (Fin 21 → ZMod 3) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' mclC) (Matrix.toLin' (toM 3 21 mclBasisInv))
    (by rw [← Matrix.toLin'_mul, mclC_mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, mclC_left_inv, Matrix.toLin'_one])

@[expose] def mclBasis : Module.Basis (Fin 21) (ZMod 3) (Fin 21 → ZMod 3) :=
  (Pi.basisFun (ZMod 3) (Fin 21)).map mclCEquiv

theorem mclBasis_apply (k : Fin 21) : mclBasis k = mclVec (mclBasisIdx.getD k 0) := by
  rw [mclBasis, Module.Basis.map_apply, Pi.basisFun_apply, ← mclC_col]
  show Matrix.toLin' mclC (Pi.single k 1) = _
  rw [Matrix.toLin'_apply, mulVec_single_one]
  rfl

@[expose] def mclFam (i : Fin 275) : Fin 21 → ZMod 3 := mclVec i

theorem mclFam_injective : Function.Injective mclFam :=
  fun i j h => Fin.ext (mclVec_inj i.2 j.2 h)

@[expose] def mclSeedsJ (k : Fin 2) : CFSG.Sporadic.McL.J :=
  if k.val = 0 then CFSG.Sporadic.McL.a else CFSG.Sporadic.McL.b

@[expose] def mclGenPerms (k : Fin 2) : Equiv.Perm (Fin 275) := mclGen k

theorem range_mclSeedsJ :
    Set.range mclSeedsJ = {CFSG.Sporadic.McL.a, CFSG.Sporadic.McL.b} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff,
    mclSeedsJ, Fin.val_zero, Fin.val_one, ite_true, one_ne_zero, ite_false]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

theorem range_mclGenPerms : Set.range mclGenPerms = {mclGen 0, mclGen 1} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

theorem closure_mclSeedsJ : Subgroup.closure (Set.range mclSeedsJ) = ⊤ := by
  rw [range_mclSeedsJ]
  exact CFSG.Sporadic.McL.closure_ab

theorem mcl_smul_def (g : CFSG.Sporadic.McL.J) (v : Fin 21 → ZMod 3) :
    g • v = CFSG.Sporadic.McL.mat g *ᵥ v := rfl

theorem mclMat_a : CFSG.Sporadic.McL.mat CFSG.Sporadic.McL.a = CFSG.Sporadic.McL.mA := rfl

theorem mclMat_b : CFSG.Sporadic.McL.mat CFSG.Sporadic.McL.b = CFSG.Sporadic.McL.mB := rfl

theorem mclSeedsJ_mk0 (h : 0 < 2) : mclSeedsJ ⟨0, h⟩ = CFSG.Sporadic.McL.a := rfl

theorem mclSeedsJ_mk1 (h : 1 < 2) : mclSeedsJ ⟨1, h⟩ = CFSG.Sporadic.McL.b := rfl

theorem mclGenPerms_mk (k : ℕ) (h : k < 2) : mclGenPerms ⟨k, h⟩ = mclGen k := rfl

theorem mclSeedsJ_smul (k : Fin 2) (i : Fin 275) :
    mclSeedsJ k • mclFam i = mclFam (mclGenPerms k i) := by
  obtain ⟨k, hk⟩ := k
  rw [mclGenPerms_mk, mcl_smul_def]
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [mclSeedsJ_mk0, mclMat_a]
    exact (mcl_seed_mulVec i).1
  · rw [mclSeedsJ_mk1, mclMat_b]
    exact (mcl_seed_mulVec i).2

theorem mcl_fix (g : CFSG.Sporadic.McL.J) (hg : ∀ i, g • mclFam i = mclFam i) : g = 1 := by
  apply CFSG.Sporadic.McL.mat_injective
  rw [CFSG.Sporadic.McL.mat_one]
  refine eq_one_of_fix_cols (CFSG.Sporadic.McL.mat g) mclC _ mclC_left_inv fun k => ?_
  rw [mclC_col]
  have := hg ⟨_, mclBasisIdx_lt k⟩
  rw [mcl_smul_def] at this
  exact this

theorem mcl_smul_mem : ∀ g : CFSG.Sporadic.McL.J, ∀ i, g • mclFam i ∈ Set.range mclFam :=
  smul_mem_range closure_mclSeedsJ mclSeedsJ_smul

theorem mclFamPerm_injective : Function.Injective (familyPerm mclFam_injective mcl_smul_mem) :=
  familyPerm_injective mclFam_injective mcl_smul_mem mcl_fix

theorem mclFamPerm_range :
    (familyPerm mclFam_injective mcl_smul_mem).range =
      Subgroup.closure (Set.range mclGenPerms) :=
  familyPerm_range mclFam_injective mcl_smul_mem closure_mclSeedsJ mclSeedsJ_smul

@[expose] def mclFamEquiv : CFSG.Sporadic.McL.J ≃* Subgroup.closure (Set.range mclGenPerms) :=
  (MonoidHom.ofInjective mclFamPerm_injective).trans (MulEquiv.subgroupCongr mclFamPerm_range)

@[expose] def mclMatEquiv : Blueprint.NativeSporadic.McL ≃* CFSG.Sporadic.McL.J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 3 21 (by norm_num) CFSG.Sporadic.McL.mA
    CFSG.Sporadic.McL.mB (CFSG.Sporadic.McL.det_mA_ne_zero CFSG.Sporadic.McL.matrixFacts)
    (CFSG.Sporadic.McL.det_mB_ne_zero CFSG.Sporadic.McL.matrixFacts)

theorem mclMatEquiv_val (u : Blueprint.NativeSporadic.McL) :
    CFSG.Sporadic.McL.mat (mclMatEquiv u) = u.val.val :=
  rfl

theorem closure_mclGenPerms : Subgroup.closure (Set.range mclGenPerms) = mclP := by
  rw [range_mclGenPerms, mclP]

@[expose] def mclPermEquiv : Blueprint.NativeSporadic.McL ≃* mclP :=
  (mclMatEquiv.trans mclFamEquiv).trans (MulEquiv.subgroupCongr closure_mclGenPerms)

theorem mclPermEquiv_apply (u : Blueprint.NativeSporadic.McL) :
    (mclPermEquiv u : Equiv.Perm (Fin 275)) =
      familyPerm mclFam_injective mcl_smul_mem (mclMatEquiv u) :=
  rfl

theorem mclVec_permEquiv (u : Blueprint.NativeSporadic.McL) (i : Fin 275) :
    mclVec ((mclPermEquiv u : Equiv.Perm (Fin 275)) i) = u.val.val *ᵥ mclVec i := by
  rw [mclPermEquiv_apply]
  have := familyPerm_apply mclFam_injective mcl_smul_mem (mclMatEquiv u) i
  rw [mcl_smul_def, mclMatEquiv_val] at this
  exact this

@[expose] def mclSeedA : Blueprint.NativeSporadic.McL := mclMatEquiv.symm CFSG.Sporadic.McL.a

@[expose] def mclSeedB : Blueprint.NativeSporadic.McL := mclMatEquiv.symm CFSG.Sporadic.McL.b

theorem mclSeedA_val : mclSeedA.val.val = CFSG.Sporadic.McL.mA := by
  rw [← mclMatEquiv_val, mclSeedA, MulEquiv.apply_symm_apply, mclMat_a]

theorem mclSeedB_val : mclSeedB.val.val = CFSG.Sporadic.McL.mB := by
  rw [← mclMatEquiv_val, mclSeedB, MulEquiv.apply_symm_apply, mclMat_b]

theorem mclPermEquiv_seedA : (mclPermEquiv mclSeedA : Equiv.Perm (Fin 275)) = mclGen 0 := by
  rw [mclPermEquiv_apply, mclSeedA, MulEquiv.apply_symm_apply]
  exact familyPerm_gen mclFam_injective mcl_smul_mem mclSeedsJ_smul 0

theorem mclPermEquiv_seedB : (mclPermEquiv mclSeedB : Equiv.Perm (Fin 275)) = mclGen 1 := by
  rw [mclPermEquiv_apply, mclSeedB, MulEquiv.apply_symm_apply]
  exact familyPerm_gen mclFam_injective mcl_smul_mem mclSeedsJ_smul 1

theorem FAM_McL_faithful_permutation_action :
    (∀ i < 275, mclVec i ≠ 0) ∧
    (∀ i < 275, ∀ j < 275, mclVec i = mclVec j → i = j) ∧
    (∃ bs : Module.Basis (Fin 21) (ZMod 3) (Fin 21 → ZMod 3),
      ∀ k : Fin 21, bs k = mclVec (mclBasisIdx.getD k 0)) ∧
    (∀ i : Fin 275, CFSG.Sporadic.McL.mA *ᵥ mclVec i = mclVec (mclGen 0 i)) ∧
    (∀ i : Fin 275, CFSG.Sporadic.McL.mB *ᵥ mclVec i = mclVec (mclGen 1 i)) ∧
    (∀ (u : Blueprint.NativeSporadic.McL) (i : Fin 275),
      mclVec ((mclPermEquiv u : Equiv.Perm (Fin 275)) i) = u.val.val *ᵥ mclVec i) ∧
    mclSeedA.val.val = CFSG.Sporadic.McL.mA ∧ mclSeedB.val.val = CFSG.Sporadic.McL.mB ∧
    (mclPermEquiv mclSeedA : Equiv.Perm (Fin 275)) = mclGen 0 ∧
    (mclPermEquiv mclSeedB : Equiv.Perm (Fin 275)) = mclGen 1 :=
  ⟨fun _ hi => mclVec_ne_zero hi, fun _ hi _ hj h => mclVec_inj hi hj h,
    ⟨mclBasis, mclBasis_apply⟩, fun i => (mcl_seed_mulVec i).1, fun i => (mcl_seed_mulVec i).2,
    mclVec_permEquiv, mclSeedA_val, mclSeedB_val, mclPermEquiv_seedA, mclPermEquiv_seedB⟩

end CFSG.Sporadic.Schreier
