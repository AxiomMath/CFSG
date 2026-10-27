module

public import CFSG.Sporadic.Schreier.PairHSCert
public import CFSG.Sporadic.Schreier.PairAction
public import CFSG.Sporadic.Schreier.PairF2Sep
public import CFSG.Sporadic.HS
public import CFSG.Blueprint.MatrixSeedIdentification
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.HS.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate2218
public import CFSG.Sporadic.Schreier.PairHSFaithfulInputs
public import Certificates.Certificate2221
public import Certificates.Certificate3167

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.J1 CFSG.Sporadic.J1.Native Matrix
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Schreier.PairF2

theorem hs_faithful_check :
    hsFaithfulWith hsVectors hsStrongArrs CFSG.Sporadic.HS.Native.hsData.rowsA
      CFSG.Sporadic.HS.Native.hsData.rowsB = true :=
  Certificates.certificate2221

@[expose] def hsBits : Array ℕ := hsVectors.map (bitsOfList 20)

@[expose] def hsBasisRows : Array ℕ := Array.ofFn (n := 20) fun k => hsBits[hsBasisIdx.getD k 0]!

theorem hs_faithful_parts :
    (∀ i < 3850, hsBits[i]! ≠ 0) ∧
    (∀ i < 3850, mulVecRows 20 CFSG.Sporadic.HS.Native.hsData.rowsA hsBits[i]! =
      hsBits[(hsStrongArrs[0]!)[i]!]!) ∧
    (∀ i < 3850, mulVecRows 20 CFSG.Sporadic.HS.Native.hsData.rowsB hsBits[i]! =
      hsBits[(hsStrongArrs[1]!)[i]!]!) ∧
    PairNative.strictInc hsBits.toList.mergeSort = true ∧
    mulRows 20 (invRowsF2 20 hsBasisRows) hsBasisRows = idRows 20 ∧
    mulRows 20 hsBasisRows (invRowsF2 20 hsBasisRows) = idRows 20 := by
  have h := hs_faithful_check
  unfold hsFaithfulWith at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, h2, h3, h4⟩
  · have := allLt_spec h1 hi
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    exact this.1.1
  · have := allLt_spec h1 hi
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    exact this.1.2
  · have := allLt_spec h1 hi
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    exact this.2

theorem hsVectors_wfV {i : ℕ} (hi : i < 3850) : wfV 2 20 hsVectors[i]! = true :=
  hsCertOK_parts.2.1 i hi

theorem hsBits_get {i : ℕ} (hi : i < 3850) : hsBits[i]! = bitsOfList 20 hsVectors[i]! := by
  have hs : hsVectors.size = 3850 := hsCertOK_parts.1
  rw [hsBits, getElem!_pos _ i (by simp [hs, hi]), Array.getElem_map,
    getElem!_pos hsVectors i (by rw [hs]; exact hi)]

theorem toVecD_bitsOfList {d : ℕ} {v : List ℕ} (hv : wfV 2 d v = true) :
    toVecD d (bitsOfList d v) = toV 2 d v := by
  funext j
  rw [bitsOfList, toVecD_ofBits]
  have hlt := (wfV_iff.1 hv).2
  have hj : j.val < v.length := by rw [(wfV_iff.1 hv).1]; exact j.2
  have hx := hlt _ (List.getElem_mem hj)
  simp only [toV, List.getD_eq_getElem _ _ hj]
  rcases (by omega : v[j.val] = 0 ∨ v[j.val] = 1) with h | h <;> rw [h] <;> rfl

theorem hsVec_eq {i : ℕ} (hi : i < 3850) : hsVec i = toVecD 20 hsBits[i]! := by
  rw [hsBits_get hi, toVecD_bitsOfList (hsVectors_wfV hi)]
  rfl

theorem hsBits_lt {i : ℕ} (hi : i < 3850) : hsBits[i]! < 2 ^ 20 := by
  rw [hsBits_get hi, bitsOfList]
  exact ofBits_lt 20 _

theorem hsVec_ne_zero {i : ℕ} (hi : i < 3850) : hsVec i ≠ 0 := by
  rw [hsVec_eq hi]
  intro h
  rw [← toVecD_zero] at h
  exact hs_faithful_parts.1 i hi (toVecD_injective (hsBits_lt hi) (by norm_num) h)

theorem hsBits_inj {i j : ℕ} (hi : i < 3850) (hj : j < 3850) (h : hsBits[i]! = hsBits[j]!) :
    i = j := by
  have hsize : hsBits.size = 3850 := by simp [hsBits, hsCertOK_parts.1]
  have hsort := pairwise_of_strictInc hs_faithful_parts.2.2.2.1
  have hnd : hsBits.toList.Nodup :=
    (List.mergeSort_perm hsBits.toList (fun a b => decide (a ≤ b))).nodup_iff.1
      (hsort.imp fun hab => Nat.ne_of_lt hab)
  have hi' : i < hsBits.toList.length := by simp [hsize, hi]
  have hj' : j < hsBits.toList.length := by simp [hsize, hj]
  rw [getElem!_pos hsBits i (by rw [hsize]; exact hi),
    getElem!_pos hsBits j (by rw [hsize]; exact hj), ← Array.getElem_toList (h := hi'),
    ← Array.getElem_toList (h := hj')] at h
  exact (List.Nodup.getElem_inj_iff hnd).1 h

theorem hsVec_inj {i j : ℕ} (hi : i < 3850) (hj : j < 3850) (h : hsVec i = hsVec j) : i = j := by
  rw [hsVec_eq hi, hsVec_eq hj] at h
  exact hsBits_inj hi hj (toVecD_injective (hsBits_lt hi) (hsBits_lt hj) h)

abbrev hsA1 : Matrix (Fin 20) (Fin 20) (ZMod 2) :=
  Blueprint.NativeSporadic.decode 2 20 1 Blueprint.NativeSporadic.HSSeed1

abbrev hsA2 : Matrix (Fin 20) (Fin 20) (ZMod 2) :=
  Blueprint.NativeSporadic.decode 2 20 1 Blueprint.NativeSporadic.HSSeed2

private theorem hsData_seedA :
    CFSG.Sporadic.HS.Native.hsData.seedA = Blueprint.NativeSporadic.HSSeed1 := rfl

private theorem hsData_seedB :
    CFSG.Sporadic.HS.Native.hsData.seedB = Blueprint.NativeSporadic.HSSeed2 := rfl

theorem hsBase : BaseFacts CFSG.Sporadic.HS.Native.hsData := CFSG.Sporadic.HS.hsFacts.toBaseFacts

theorem mA_hsData : mA CFSG.Sporadic.HS.Native.hsData = hsA1 := by
  show Blueprint.NativeSporadic.decode 2 20 1 CFSG.Sporadic.HS.Native.hsData.seedA = _
  rw [hsData_seedA]

theorem mB_hsData : mB CFSG.Sporadic.HS.Native.hsData = hsA2 := by
  show Blueprint.NativeSporadic.decode 2 20 1 CFSG.Sporadic.HS.Native.hsData.seedB = _
  rw [hsData_seedB]

theorem rowsMatrix_hsRowsA : rowsMatrix 20 CFSG.Sporadic.HS.Native.hsData.rowsA = hsA1 := by
  rw [← mA_hsData]
  exact rowsMatrix_rowsA CFSG.Sporadic.HS.Native.hsData

theorem rowsMatrix_hsRowsB : rowsMatrix 20 CFSG.Sporadic.HS.Native.hsData.rowsB = hsA2 := by
  rw [← mB_hsData]
  exact rowsMatrix_rowsB CFSG.Sporadic.HS.Native.hsData

theorem det_hsA1 : hsA1.det ≠ 0 := by
  rw [← mA_hsData]
  exact det_mA_ne_zero hsBase

theorem det_hsA2 : hsA2.det ≠ 0 := by
  rw [← mB_hsData]
  exact det_mB_ne_zero hsBase

@[expose] def hsGA : GL (Fin 20) (ZMod 2) := Matrix.GeneralLinearGroup.mkOfDetNeZero hsA1 det_hsA1

@[expose] def hsGB : GL (Fin 20) (ZMod 2) := Matrix.GeneralLinearGroup.mkOfDetNeZero hsA2 det_hsA2

abbrev hsJ : Subgroup (GL (Fin 20) (ZMod 2)) := Subgroup.closure {hsGA, hsGB}

abbrev hsMat (g : hsJ) : Matrix (Fin 20) (Fin 20) (ZMod 2) :=
  ((g : GL (Fin 20) (ZMod 2)) : Matrix (Fin 20) (Fin 20) (ZMod 2))

@[expose] def hsa : hsJ := ⟨hsGA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] def hsb : hsJ := ⟨hsGB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem hsMat_a : hsMat hsa = hsA1 := rfl

theorem hsMat_b : hsMat hsb = hsA2 := rfl

theorem hs_closure_ab : Subgroup.closure ({hsa, hsb} : Set hsJ) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({hsGA, hsGB} : Set (GL (Fin 20) (ZMod 2)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [hsa, hsb]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

theorem hsA1_mulVec {i : ℕ} (hi : i < 3850) : hsA1 *ᵥ hsVec i = hsVec (hsStrongArrs[0]!)[i]! := by
  have hlt : (hsStrongArrs[0]!)[i]! < 3850 := by
    have := rep_hsStrongPerm (by norm_num : 0 < 8) ⟨i, hi⟩
    rw [show (hsStrongArrs[0]!)[i]! = (hsStrongArrs[0]!)[((⟨i, hi⟩ : Fin 3850) : ℕ)]! from rfl,
      this]
    exact Fin.isLt _
  rw [hsVec_eq hi, hsVec_eq hlt, ← rowsMatrix_hsRowsA, ← toVecD_mulVecRows,
    hs_faithful_parts.2.1 i hi]

theorem hsA2_mulVec {i : ℕ} (hi : i < 3850) : hsA2 *ᵥ hsVec i = hsVec (hsStrongArrs[1]!)[i]! := by
  have hlt : (hsStrongArrs[1]!)[i]! < 3850 := by
    have := rep_hsStrongPerm (by norm_num : 1 < 8) ⟨i, hi⟩
    rw [show (hsStrongArrs[1]!)[i]! = (hsStrongArrs[1]!)[((⟨i, hi⟩ : Fin 3850) : ℕ)]! from rfl,
      this]
    exact Fin.isLt _
  rw [hsVec_eq hi, hsVec_eq hlt, ← rowsMatrix_hsRowsB, ← toVecD_mulVecRows,
    hs_faithful_parts.2.2.1 i hi]

theorem rep_hsGen {k : ℕ} (hk : k < 8) : Rep 3850 hsStrongArrs[k]! (hsGen k) :=
  rep_hsStrongPerm hk

theorem hs_seed_mulVec (i : Fin 3850) :
    hsA1 *ᵥ hsVec i = hsVec (hsGen 0 i) ∧ hsA2 *ᵥ hsVec i = hsVec (hsGen 1 i) := by
  refine ⟨?_, ?_⟩
  · rw [hsA1_mulVec i.2, rep_hsGen (by norm_num : 0 < 8) i]
  · rw [hsA2_mulVec i.2, rep_hsGen (by norm_num : 1 < 8) i]

@[expose] def hsC : Matrix (Fin 20) (Fin 20) (ZMod 2) := (rowsMatrix 20 hsBasisRows)ᵀ

theorem hsBasisIdx_lt (k : Fin 20) : hsBasisIdx.getD k 0 < 3850 := by
  fin_cases k <;> simp [hsBasisIdx]

theorem hsBasisRows_get (k : Fin 20) :
    hsBasisRows[(k : ℕ)]?.getD 0 = hsBits[hsBasisIdx.getD k 0]! := by
  rw [hsBasisRows, Array.getElem?_ofFn, dite_eq_left k.2, Option.getD_some]

theorem hsC_col (k : Fin 20) : (fun i => hsC i k) = hsVec (hsBasisIdx.getD k 0) := by
  funext i
  rw [hsVec_eq (hsBasisIdx_lt k), hsC, Matrix.transpose_apply, rowsMatrix_apply, hsBasisRows_get]

@[expose] def hsQ : Matrix (Fin 20) (Fin 20) (ZMod 2) := (rowsMatrix 20 (invRowsF2 20 hsBasisRows))ᵀ

theorem hsQ_mul_C : hsQ * hsC = 1 := by
  have h1 : rowsMatrix 20 hsBasisRows * rowsMatrix 20 (invRowsF2 20 hsBasisRows) = 1 := by
    rw [← rowsMatrix_mulRows, hs_faithful_parts.2.2.2.2.2, rowsMatrix_idRows]
  have h3 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, Matrix.transpose_one] at h3
  exact h3

theorem hsC_mul_Q : hsC * hsQ = 1 := by
  have h1 : rowsMatrix 20 (invRowsF2 20 hsBasisRows) * rowsMatrix 20 hsBasisRows = 1 := by
    rw [← rowsMatrix_mulRows, hs_faithful_parts.2.2.2.2.1, rowsMatrix_idRows]
  have h3 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, Matrix.transpose_one] at h3
  exact h3

@[expose] def hsCEquiv : (Fin 20 → ZMod 2) ≃ₗ[ZMod 2] (Fin 20 → ZMod 2) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' hsC) (Matrix.toLin' hsQ)
    (by rw [← Matrix.toLin'_mul, hsC_mul_Q, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, hsQ_mul_C, Matrix.toLin'_one])

@[expose] def hsBasis : Module.Basis (Fin 20) (ZMod 2) (Fin 20 → ZMod 2) :=
  (Pi.basisFun (ZMod 2) (Fin 20)).map hsCEquiv

theorem hsBasis_apply (k : Fin 20) : hsBasis k = hsVec (hsBasisIdx.getD k 0) := by
  rw [hsBasis, Module.Basis.map_apply, Pi.basisFun_apply, ← hsC_col]
  show Matrix.toLin' hsC (Pi.single k 1) = _
  rw [Matrix.toLin'_apply, mulVec_single_one]
  rfl

@[expose] def hsFam (i : Fin 3850) : Fin 20 → ZMod 2 := hsVec i

theorem hsFam_injective : Function.Injective hsFam :=
  fun i j h => Fin.ext (hsVec_inj i.2 j.2 h)

@[expose] def hsSeedsJ (k : Fin 2) : hsJ := if k.val = 0 then hsa else hsb

@[expose] def hsGenPerms (k : Fin 2) : Equiv.Perm (Fin 3850) := hsGen k

theorem range_hsSeedsJ : Set.range hsSeedsJ = {hsa, hsb} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff,
    hsSeedsJ, Fin.val_zero, Fin.val_one, ite_true, one_ne_zero, ite_false]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

theorem range_hsGenPerms : Set.range hsGenPerms = {hsGen 0, hsGen 1} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

theorem closure_hsSeedsJ : Subgroup.closure (Set.range hsSeedsJ) = ⊤ := by
  rw [range_hsSeedsJ]
  exact hs_closure_ab

theorem hs_smul_def (g : hsJ) (v : Fin 20 → ZMod 2) : g • v = hsMat g *ᵥ v := rfl

theorem hsSeedsJ_mk0 (h : 0 < 2) : hsSeedsJ ⟨0, h⟩ = hsa := rfl

theorem hsSeedsJ_mk1 (h : 1 < 2) : hsSeedsJ ⟨1, h⟩ = hsb := rfl

theorem hsGenPerms_mk (k : ℕ) (h : k < 2) : hsGenPerms ⟨k, h⟩ = hsGen k := rfl

theorem hsSeedsJ_smul (k : Fin 2) (i : Fin 3850) :
    hsSeedsJ k • hsFam i = hsFam (hsGenPerms k i) := by
  obtain ⟨k, hk⟩ := k
  rw [hsGenPerms_mk, hs_smul_def]
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [hsSeedsJ_mk0, hsMat_a]
    exact (hs_seed_mulVec i).1
  · rw [hsSeedsJ_mk1, hsMat_b]
    exact (hs_seed_mulVec i).2

theorem hsMat_injective : Function.Injective hsMat :=
  fun _ _ e => Subtype.ext (Units.ext e)

theorem hs_fix (g : hsJ) (hg : ∀ i, g • hsFam i = hsFam i) : g = 1 := by
  apply hsMat_injective
  show hsMat g = 1
  refine eq_one_of_fix_cols (hsMat g) hsC hsQ hsQ_mul_C fun k => ?_
  rw [hsC_col]
  have := hg ⟨_, hsBasisIdx_lt k⟩
  rw [hs_smul_def] at this
  exact this

theorem hs_smul_mem : ∀ g : hsJ, ∀ i, g • hsFam i ∈ Set.range hsFam :=
  smul_mem_range closure_hsSeedsJ hsSeedsJ_smul

theorem hsFamPerm_injective : Function.Injective (familyPerm hsFam_injective hs_smul_mem) :=
  familyPerm_injective hsFam_injective hs_smul_mem hs_fix

theorem hsFamPerm_range :
    (familyPerm hsFam_injective hs_smul_mem).range = Subgroup.closure (Set.range hsGenPerms) :=
  familyPerm_range hsFam_injective hs_smul_mem closure_hsSeedsJ hsSeedsJ_smul

@[expose] def hsFamEquiv : hsJ ≃* Subgroup.closure (Set.range hsGenPerms) :=
  (MonoidHom.ofInjective hsFamPerm_injective).trans (MulEquiv.subgroupCongr hsFamPerm_range)

@[expose] def hsMatEquiv : Blueprint.NativeSporadic.HS ≃* hsJ :=
  Blueprint.NativeSporadic.matrixSeedEquiv 2 20 (by norm_num) hsA1 hsA2 det_hsA1 det_hsA2

theorem hsMatEquiv_val (u : Blueprint.NativeSporadic.HS) : hsMat (hsMatEquiv u) = u.val.val :=
  rfl

theorem closure_hsGenPerms : Subgroup.closure (Set.range hsGenPerms) = hsP := by
  rw [range_hsGenPerms, hsP]

@[expose] def hsPermEquiv : Blueprint.NativeSporadic.HS ≃* hsP :=
  (hsMatEquiv.trans hsFamEquiv).trans (MulEquiv.subgroupCongr closure_hsGenPerms)

theorem hsPermEquiv_apply (u : Blueprint.NativeSporadic.HS) :
    (hsPermEquiv u : Equiv.Perm (Fin 3850)) =
      familyPerm hsFam_injective hs_smul_mem (hsMatEquiv u) :=
  rfl

theorem hsVec_permEquiv (u : Blueprint.NativeSporadic.HS) (i : Fin 3850) :
    hsVec ((hsPermEquiv u : Equiv.Perm (Fin 3850)) i) = u.val.val *ᵥ hsVec i := by
  rw [hsPermEquiv_apply]
  have := familyPerm_apply hsFam_injective hs_smul_mem (hsMatEquiv u) i
  rw [hs_smul_def, hsMatEquiv_val] at this
  exact this

@[expose] def hsSeedA : Blueprint.NativeSporadic.HS := hsMatEquiv.symm hsa

@[expose] def hsSeedB : Blueprint.NativeSporadic.HS := hsMatEquiv.symm hsb

theorem hsSeedA_val : hsSeedA.val.val = hsA1 := by
  rw [← hsMatEquiv_val, hsSeedA, MulEquiv.apply_symm_apply, hsMat_a]

theorem hsSeedB_val : hsSeedB.val.val = hsA2 := by
  rw [← hsMatEquiv_val, hsSeedB, MulEquiv.apply_symm_apply, hsMat_b]

theorem hsPermEquiv_seedA : (hsPermEquiv hsSeedA : Equiv.Perm (Fin 3850)) = hsGen 0 := by
  rw [hsPermEquiv_apply, hsSeedA, MulEquiv.apply_symm_apply]
  exact familyPerm_gen hsFam_injective hs_smul_mem hsSeedsJ_smul 0

theorem hsPermEquiv_seedB : (hsPermEquiv hsSeedB : Equiv.Perm (Fin 3850)) = hsGen 1 := by
  rw [hsPermEquiv_apply, hsSeedB, MulEquiv.apply_symm_apply]
  exact familyPerm_gen hsFam_injective hs_smul_mem hsSeedsJ_smul 1

theorem FAM_HS_faithful_permutation_action :
    (∀ i < 3850, hsVec i ≠ 0) ∧
    (∀ i < 3850, ∀ j < 3850, hsVec i = hsVec j → i = j) ∧
    (∃ bs : Module.Basis (Fin 20) (ZMod 2) (Fin 20 → ZMod 2),
      ∀ k : Fin 20, bs k = hsVec (hsBasisIdx.getD k 0)) ∧
    (∀ i : Fin 3850, hsA1 *ᵥ hsVec i = hsVec (hsGen 0 i)) ∧
    (∀ i : Fin 3850, hsA2 *ᵥ hsVec i = hsVec (hsGen 1 i)) ∧
    (∀ (u : Blueprint.NativeSporadic.HS) (i : Fin 3850),
      hsVec ((hsPermEquiv u : Equiv.Perm (Fin 3850)) i) = u.val.val *ᵥ hsVec i) ∧
    hsSeedA.val.val = hsA1 ∧ hsSeedB.val.val = hsA2 ∧
    (hsPermEquiv hsSeedA : Equiv.Perm (Fin 3850)) = hsGen 0 ∧
    (hsPermEquiv hsSeedB : Equiv.Perm (Fin 3850)) = hsGen 1 :=
  ⟨fun _ hi => hsVec_ne_zero hi, fun _ hi _ hj h => hsVec_inj hi hj h,
    ⟨hsBasis, hsBasis_apply⟩, fun i => (hs_seed_mulVec i).1, fun i => (hs_seed_mulVec i).2,
    hsVec_permEquiv, hsSeedA_val, hsSeedB_val, hsPermEquiv_seedA, hsPermEquiv_seedB⟩

end CFSG.Sporadic.Schreier
