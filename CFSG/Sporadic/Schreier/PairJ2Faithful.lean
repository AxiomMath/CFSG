module

public import CFSG.Sporadic.Schreier.PairJ2Cert
public import CFSG.Sporadic.Schreier.PairAction
public import CFSG.Sporadic.J2.Setup
public import CFSG.Blueprint.MatrixSeedIdentification
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import CFSG.Blueprint.NativeSporadic
public meta import CFSG.Sporadic.Schreier.PairJ2Cert
public meta import Certificates.Data.CFSGNative.J1.Vec
public meta import Certificates.Data.CFSGNative.J2.Certificate
public import Certificates.Certificate2233
public import CFSG.Sporadic.Schreier.PairJ2FaithfulInputs
public import Certificates.Certificate2235
public import Certificates.Certificate3139

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.J1 CFSG.Sporadic.J1.Native Matrix

local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem j2FaithfulOK_eq : j2FaithfulOK = true :=
  Certificates.certificate2235

theorem j2FaithfulOK_parts :
    (∀ i < 315, j2Vectors[i]!.any (· != 0) = true) ∧
    (∀ i < 315, ∀ j < i, j2Vectors[i]! ≠ j2Vectors[j]!) ∧
    (∀ i < 315, mvL 5 CFSG.Sporadic.J2.Native.mA j2Vectors[i]! =
      j2Vectors[(j2StrongArrs[0]!)[i]!]!) ∧
    (∀ i < 315, mvL 5 CFSG.Sporadic.J2.Native.mB j2Vectors[i]! =
      j2Vectors[(j2StrongArrs[1]!)[i]!]!) ∧
    wfM 14 j2BasisInv = true ∧ mulL 5 14 j2BasisInv j2BasisMat = idL 14 := by
  have h := j2FaithfulOK_eq
  simp only [j2FaithfulOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun i hi => allLt_spec h1 hi, fun i hi j hj => ?_, fun i hi => ?_, fun i hi => ?_, h4,
    h5⟩
  · have := allLt_spec (allLt_spec h2 hi) hj
    simpa using this
  · have := allLt_spec h3 hi
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  · have := allLt_spec h3 hi
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.2

theorem j2Vectors_wfV {i : ℕ} (hi : i < 315) : wfV 5 14 j2Vectors[i]! = true :=
  j2CertOK_parts.2.1 i hi

theorem j2Vectors_length {i : ℕ} (hi : i < 315) : j2Vectors[i]!.length = 14 :=
  (wfV_iff.1 (j2Vectors_wfV hi)).1

theorem j2Vec_ne_zero {i : ℕ} (hi : i < 315) : j2Vec i ≠ 0 := by
  have h := j2FaithfulOK_parts.1 i hi
  obtain ⟨x, hx, hx0⟩ := List.any_eq_true.1 h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have hk14 : k < 14 := by rw [← j2Vectors_length hi]; exact hk
  intro h0
  have h1 := congrFun h0 ⟨k, hk14⟩
  have hlt := (wfV_iff.1 (j2Vectors_wfV hi)).2 _ (List.getElem_mem hk)
  simp only [j2Vec, toV, Pi.zero_apply] at h1
  rw [List.getD_eq_getElem _ _ hk] at h1
  have h2 := congrArg ZMod.val h1
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ZMod.val_zero] at h2
  simp [h2] at hx0

theorem j2Vec_inj {i j : ℕ} (hi : i < 315) (hj : j < 315) (h : j2Vec i = j2Vec j) : i = j := by
  have he := toV_inj (j2Vectors_wfV hi) (j2Vectors_wfV hj) h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact j2FaithfulOK_parts.2.1 j hj i hlt he.symm
  · exact j2FaithfulOK_parts.2.1 i hi j hlt he

abbrev j2A1 : Matrix (Fin 14) (Fin 14) (ZMod 5) :=
  Blueprint.NativeSporadic.decode 5 14 1 Blueprint.NativeSporadic.J2Seed1

abbrev j2A2 : Matrix (Fin 14) (Fin 14) (ZMod 5) :=
  Blueprint.NativeSporadic.decode 5 14 1 Blueprint.NativeSporadic.J2Seed2

theorem mat_j2a : J2.mat J2.a = j2A1 := by
  rw [J2.mat_a]
  show _ = Blueprint.NativeSporadic.decode 5 14 1 Blueprint.NativeSporadic.J2Seed1
  rw [Bridge.J2.decode_seed₁]
  rfl

theorem mat_j2b : J2.mat J2.b = j2A2 := by
  rw [J2.mat_b]
  show _ = Blueprint.NativeSporadic.decode 5 14 1 Blueprint.NativeSporadic.J2Seed2
  rw [Bridge.J2.decode_seed₂]
  rfl

theorem j2A1_mulVec {i : ℕ} (hi : i < 315) :
    j2A1 *ᵥ j2Vec i = j2Vec (j2StrongArrs[0]!)[i]! := by
  rw [← mat_j2a, J2.mat_a, j2Vec, ← toV_mvL J2.matrix_parts.1 (j2Vectors_length hi),
    j2FaithfulOK_parts.2.2.1 i hi]
  rfl

theorem j2A2_mulVec {i : ℕ} (hi : i < 315) :
    j2A2 *ᵥ j2Vec i = j2Vec (j2StrongArrs[1]!)[i]! := by
  rw [← mat_j2b, J2.mat_b, j2Vec, ← toV_mvL J2.matrix_parts.2.1 (j2Vectors_length hi),
    j2FaithfulOK_parts.2.2.2.1 i hi]
  rfl

theorem j2_seed_mulVec (i : Fin 315) :
    j2A1 *ᵥ j2Vec i = j2Vec (j2Gen 0 i) ∧ j2A2 *ᵥ j2Vec i = j2Vec (j2Gen 1 i) := by
  refine ⟨?_, ?_⟩
  · rw [j2A1_mulVec i.2, rep_j2StrongPerm (by norm_num : 0 < 7) i, j2Gen]
  · rw [j2A2_mulVec i.2, rep_j2StrongPerm (by norm_num : 1 < 7) i, j2Gen]

theorem det_ne_zero_of_pow_eq_one {M : Matrix (Fin 14) (Fin 14) (ZMod 5)} {e : ℕ} (he : 0 < e)
    (h : M ^ e = 1) : M.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_pow, h0, zero_pow (Nat.pos_iff_ne_zero.mp he), Matrix.det_one] at this
  exact zero_ne_one this

theorem det_j2A1 : j2A1.det ≠ 0 :=
  det_ne_zero_of_pow_eq_one (e := 2) (by norm_num) (by rw [← mat_j2a, ← J2.mat_pow, J2.a_sq,
    J2.mat_one])

theorem det_j2A2 : j2A2.det ≠ 0 :=
  det_ne_zero_of_pow_eq_one (e := 3) (by norm_num) (by rw [← mat_j2b, ← J2.mat_pow, J2.b_cube,
    J2.mat_one])

abbrev j2C : Matrix (Fin 14) (Fin 14) (ZMod 5) := toM 5 14 j2BasisMat

theorem j2BasisMat_wfM : wfM 14 j2BasisMat = true := wfM_colMat (by simp [j2BasisIdx])

theorem j2C_left_inv : toM 5 14 j2BasisInv * j2C = 1 := by
  show toM 5 14 j2BasisInv * toM 5 14 j2BasisMat = 1
  rw [← toM_mulL j2FaithfulOK_parts.2.2.2.2.1 j2BasisMat_wfM, j2FaithfulOK_parts.2.2.2.2.2,
    toM_idL]

theorem j2C_col (k : Fin 14) : (fun i => j2C i k) = j2Vec (j2BasisIdx.getD k 0) := by
  funext i
  show toM 5 14 (colMat 14 (j2BasisIdx.map fun i => j2Vectors[i]!)) i k = _
  rw [toM_colMat_apply _ i k (by simp [j2BasisIdx])]
  rw [List.getD_eq_getElem _ _ (by simp [j2BasisIdx]), List.getElem_map,
    List.getD_eq_getElem _ _ (by simp [j2BasisIdx])]
  rfl

@[expose] def j2Basis : Module.Basis (Fin 14) (ZMod 5) (Fin 14 → ZMod 5) :=
  (Pi.basisFun (ZMod 5) (Fin 14)).map
    (j2C.toLinearEquiv' (invertibleOfLeftInverse _ _ j2C_left_inv))

theorem j2Basis_apply (k : Fin 14) : j2Basis k = j2Vec (j2BasisIdx.getD k 0) := by
  rw [j2Basis, Module.Basis.map_apply, Pi.basisFun_apply, ← j2C_col]
  show Matrix.toLin' j2C (Pi.single k 1) = _
  rw [Matrix.toLin'_apply, mulVec_single_one]
  rfl

@[expose] def j2Fam (i : Fin 315) : Fin 14 → ZMod 5 := j2Vec i

theorem j2Fam_injective : Function.Injective j2Fam :=
  fun i j h => Fin.ext (j2Vec_inj i.2 j.2 h)

@[expose] def j2SeedsJ : Fin 2 → J2.J := ![J2.a, J2.b]

@[expose] def j2GenPerms : Fin 2 → Equiv.Perm (Fin 315) := ![j2Gen 0, j2Gen 1]

theorem range_j2SeedsJ : Set.range j2SeedsJ = {J2.a, J2.b} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff]
  simp only [j2SeedsJ, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

theorem range_j2GenPerms : Set.range j2GenPerms = {j2Gen 0, j2Gen 1} := by
  have key : ∀ a b : Equiv.Perm (Fin 315), Set.range ![a, b] = {a, b} := by
    intro a b
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
  exact key _ _

theorem closure_j2SeedsJ : Subgroup.closure (Set.range j2SeedsJ) = ⊤ := by
  rw [range_j2SeedsJ]
  exact J2.closure_ab

theorem j2SeedsJ_smul (k : Fin 2) (i : Fin 315) :
    j2SeedsJ k • j2Fam i = j2Fam (j2GenPerms k i) := by
  have key : ∀ (p q : Equiv.Perm (Fin 315)), (∀ i : Fin 315, J2.a • j2Fam i = j2Fam (p i)) →
      (∀ i : Fin 315, J2.b • j2Fam i = j2Fam (q i)) →
      ∀ k i, ![J2.a, J2.b] k • j2Fam i = j2Fam (![p, q] k i) := by
    intro p q hp hq k i
    fin_cases k
    · exact hp i
    · exact hq i
  refine key (j2Gen 0) (j2Gen 1) (fun i => ?_) (fun i => ?_) k i
  · rw [J2.smul_def, mat_j2a]; exact (j2_seed_mulVec i).1
  · rw [J2.smul_def, mat_j2b]; exact (j2_seed_mulVec i).2

theorem j2_fix (g : J2.J) (hg : ∀ i, g • j2Fam i = j2Fam i) : g = 1 := by
  apply J2.mat_injective
  rw [J2.mat_one]
  refine eq_one_of_fix_cols (J2.mat g) j2C _ j2C_left_inv fun k => ?_
  rw [j2C_col]
  have hk : j2BasisIdx.getD k 0 < 315 := by
    fin_cases k <;> simp [j2BasisIdx]
  have := hg ⟨_, hk⟩
  rw [J2.smul_def] at this
  exact this

theorem j2_smul_mem : ∀ g : J2.J, ∀ i, g • j2Fam i ∈ Set.range j2Fam :=
  smul_mem_range closure_j2SeedsJ j2SeedsJ_smul

theorem j2FamPerm_injective : Function.Injective (familyPerm j2Fam_injective j2_smul_mem) :=
  familyPerm_injective j2Fam_injective j2_smul_mem j2_fix

theorem j2FamPerm_range :
    (familyPerm j2Fam_injective j2_smul_mem).range = Subgroup.closure (Set.range j2GenPerms) :=
  familyPerm_range j2Fam_injective j2_smul_mem closure_j2SeedsJ j2SeedsJ_smul

@[expose] def j2FamEquiv : J2.J ≃* Subgroup.closure (Set.range j2GenPerms) :=
  (MonoidHom.ofInjective j2FamPerm_injective).trans (MulEquiv.subgroupCongr j2FamPerm_range)

theorem j2J_eq :
    Subgroup.closure {Matrix.GeneralLinearGroup.mkOfDetNeZero j2A1 det_j2A1,
      Matrix.GeneralLinearGroup.mkOfDetNeZero j2A2 det_j2A2} = J2.J := by
  have e1 : Matrix.GeneralLinearGroup.mkOfDetNeZero j2A1 det_j2A1 = Bridge.J2.uA :=
    Units.ext (mat_j2a.symm)
  have e2 : Matrix.GeneralLinearGroup.mkOfDetNeZero j2A2 det_j2A2 = Bridge.J2.uB :=
    Units.ext (mat_j2b.symm)
  rw [e1, e2]

@[expose] def j2MatEquiv : Blueprint.NativeSporadic.J2 ≃* J2.J :=
  (Blueprint.NativeSporadic.matrixSeedEquiv 5 14 (by norm_num) j2A1 j2A2 det_j2A1
    det_j2A2).trans (MulEquiv.subgroupCongr j2J_eq)

theorem j2MatEquiv_val (u : Blueprint.NativeSporadic.J2) :
    J2.mat (j2MatEquiv u) = u.val.val :=
  rfl

theorem closure_j2GenPerms : Subgroup.closure (Set.range j2GenPerms) = j2P := by
  rw [range_j2GenPerms, j2P]

@[expose] def j2PermEquiv : Blueprint.NativeSporadic.J2 ≃* j2P :=
  (j2MatEquiv.trans j2FamEquiv).trans (MulEquiv.subgroupCongr closure_j2GenPerms)

theorem j2PermEquiv_apply (u : Blueprint.NativeSporadic.J2) :
    (j2PermEquiv u : Equiv.Perm (Fin 315)) =
      familyPerm j2Fam_injective j2_smul_mem (j2MatEquiv u) :=
  rfl

theorem j2Vec_permEquiv (u : Blueprint.NativeSporadic.J2) (i : Fin 315) :
    j2Vec ((j2PermEquiv u : Equiv.Perm (Fin 315)) i) = u.val.val *ᵥ j2Vec i := by
  rw [j2PermEquiv_apply]
  have := familyPerm_apply j2Fam_injective j2_smul_mem (j2MatEquiv u) i
  rw [J2.smul_def, j2MatEquiv_val] at this
  exact this

@[expose] def j2SeedA : Blueprint.NativeSporadic.J2 := j2MatEquiv.symm J2.a

@[expose] def j2SeedB : Blueprint.NativeSporadic.J2 := j2MatEquiv.symm J2.b

theorem j2SeedA_val : j2SeedA.val.val = j2A1 := by
  rw [← j2MatEquiv_val, j2SeedA, MulEquiv.apply_symm_apply, mat_j2a]

theorem j2SeedB_val : j2SeedB.val.val = j2A2 := by
  rw [← j2MatEquiv_val, j2SeedB, MulEquiv.apply_symm_apply, mat_j2b]

theorem j2PermEquiv_seedA : (j2PermEquiv j2SeedA : Equiv.Perm (Fin 315)) = j2Gen 0 := by
  rw [j2PermEquiv_apply, j2SeedA, MulEquiv.apply_symm_apply]
  exact familyPerm_gen j2Fam_injective j2_smul_mem j2SeedsJ_smul 0

theorem j2PermEquiv_seedB : (j2PermEquiv j2SeedB : Equiv.Perm (Fin 315)) = j2Gen 1 := by
  rw [j2PermEquiv_apply, j2SeedB, MulEquiv.apply_symm_apply]
  exact familyPerm_gen j2Fam_injective j2_smul_mem j2SeedsJ_smul 1

theorem FAM_J2_faithful_permutation_action :
    (∀ i < 315, j2Vec i ≠ 0) ∧
    (∀ i < 315, ∀ j < 315, j2Vec i = j2Vec j → i = j) ∧
    (∃ b : Module.Basis (Fin 14) (ZMod 5) (Fin 14 → ZMod 5),
      ∀ k : Fin 14, b k = j2Vec (j2BasisIdx.getD k 0)) ∧
    (∀ i : Fin 315, j2A1 *ᵥ j2Vec i = j2Vec (j2Gen 0 i)) ∧
    (∀ i : Fin 315, j2A2 *ᵥ j2Vec i = j2Vec (j2Gen 1 i)) ∧
    (∀ (u : Blueprint.NativeSporadic.J2) (i : Fin 315),
      j2Vec ((j2PermEquiv u : Equiv.Perm (Fin 315)) i) = u.val.val *ᵥ j2Vec i) ∧
    j2SeedA.val.val = j2A1 ∧ j2SeedB.val.val = j2A2 ∧
    (j2PermEquiv j2SeedA : Equiv.Perm (Fin 315)) = j2Gen 0 ∧
    (j2PermEquiv j2SeedB : Equiv.Perm (Fin 315)) = j2Gen 1 :=
  ⟨fun _ hi => j2Vec_ne_zero hi, fun _ hi _ hj h => j2Vec_inj hi hj h,
    ⟨j2Basis, j2Basis_apply⟩, fun i => (j2_seed_mulVec i).1, fun i => (j2_seed_mulVec i).2,
    j2Vec_permEquiv, j2SeedA_val, j2SeedB_val, j2PermEquiv_seedA, j2PermEquiv_seedB⟩

end CFSG.Sporadic.Schreier
