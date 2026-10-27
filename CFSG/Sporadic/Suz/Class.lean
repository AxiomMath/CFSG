module

public import CFSG.Sporadic.Suz.Minus
public import CFSG.Sporadic.Th.OrbitSpec
public import CFSG.Sporadic.Suz.W64Spec

public section

namespace CFSG.Sporadic.Suz

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.VecOrbit Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem wA_size : wA.size = 64 := by unfold wA; rw [Array.size_map, matA_size]

theorem wB_size : wB.size = 64 := by unfold wB; rw [Array.size_map, matB_size]

theorem toVM_wA : toVM wA = matA := toVM_rowsOf (d := 64) (by norm_num) Native.seedA

theorem toVM_wB : toVM wB = matB := toVM_rowsOf (d := 64) (by norm_num) Native.seedB

theorem toVM_wBi : toVM wBi = mul 64 matB matB := by
  unfold wBi; rw [toVM_mulW, toVM_wB]

theorem toMatW_wA : toMatW wA = mA := by rw [toMatW, toVM_wA, toMat_matA]

theorem toMatW_wB : toMatW wB = mB := by rw [toMatW, toVM_wB, toMat_matB]

theorem toMatW_wBi : toMatW wBi = mB * mB := by
  rw [toMatW, toVM_wBi, toMat_mul matB_size rowsWF_matB rowsWF_matB, toMat_matB]

theorem conjFacts : WConjFacts wRoot wA wA wB wBi orb := by
  have hBi : RowsWF (toVM wBi) := by rw [toVM_wBi]; exact RowsWF.mul _ 64 rowsWF_matB rowsWF_matB
  have hA2 : toMatW wA * toMatW wA = 1 := by rw [toMatW_wA]; exact matrixFacts.A_sq
  have hB3 : toMatW wB ^ 3 = 1 := by rw [toMatW_wB]; exact matrixFacts.B_cube
  have hBi3 : toMatW wBi ^ 3 = 1 := by
    rw [toMatW_wBi, ← pow_two, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul,
      matrixFacts.B_cube, one_pow]
  exact conjOrbitOKW_facts wA_size (by rw [toVM_wA]; exact rowsWF_matA)
    (by rw [toVM_wA]; exact rowsWF_matA) wB_size (by rw [toVM_wB]; exact rowsWF_matB) hBi hA2 hA2
    hB3 hBi3 certificate_parts.2.2.1

theorem actionChecks_parts :
    orb.keys.size = 22880 ∧ orb.alpha.size = 22880 ∧
    orb.beta.size = 22880 ∧ invOK 22880 orb.beta (invT 22880 orb.beta) = true ∧
    sepOK 64 (sepIdx.map fun r => toVM orb.keys[r]!) sepTerms sepVec sepK sepP sepTinv
      sepTree = true ∧
    (∀ r ∈ sepIdx, r < 22880) ∧
    CFSG.Perm.Native.chainOK 22880 (chainLetters orb) chainBase chainQ chainQb
      (CFSG.Perm.Native.chainTrees 22880 (chainLetters orb) chainBase) 3 = true ∧
    CFSG.Perm.Native.orbitSizes (CFSG.Perm.Native.chainTrees 22880 (chainLetters orb) chainBase) =
      [22880, 8505, 144, 16] ∧
    CFSG.Perm.Native.treeOK 22880 subRoots[0]!
      (CFSG.Perm.Native.treeBFS 22880 subRoots[0]! (chainLetters orb)
        (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1))
      (chainLetters orb) (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1) = true ∧
    (CFSG.Perm.Native.treeBFS 22880 subRoots[0]! (chainLetters orb)
      (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1)).pts.size = 13608 ∧
    CFSG.Perm.Native.treeOK 22880 subRoots[1]!
      (CFSG.Perm.Native.treeBFS 22880 subRoots[1]! (chainLetters orb)
        (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1))
      (chainLetters orb) (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1) = true ∧
    (CFSG.Perm.Native.treeBFS 22880 subRoots[1]! (chainLetters orb)
      (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1)).pts.size = 280 ∧
    CFSG.Perm.Native.treeOK 22880 subRoots[2]!
      (CFSG.Perm.Native.treeBFS 22880 subRoots[2]! (chainLetters orb)
        (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1))
      (chainLetters orb) (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1) = true ∧
    (CFSG.Perm.Native.treeBFS 22880 subRoots[2]! (chainLetters orb)
      (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1)).pts.size = 486 ∧
    ∀ p < 22880, p = 0 ∨
      inT (CFSG.Perm.Native.chainTrees 22880 (chainLetters orb) chainBase)[1]! p = true ∨
      inT (CFSG.Perm.Native.treeBFS 22880 subRoots[0]! (chainLetters orb)
        (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1)) p = true ∨
      inT (CFSG.Perm.Native.treeBFS 22880 subRoots[1]! (chainLetters orb)
        (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1)) p = true ∨
      inT (CFSG.Perm.Native.treeBFS 22880 subRoots[2]! (chainLetters orb)
        (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1)) p = true := by
  have h := certificate_parts.2.2.2
  unfold actionChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun r hr => ?_, h7, h8, h9, h10, h11, h12, h13, h14,
    fun p hp => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hr
    exact h6 i hi
  · have := (allIn_eq_true.1 h15) p (Nat.zero_le _) hp
    simpa only [Bool.or_eq_true, beq_iff_eq, or_assoc] using this

theorem orb_size : orb.keys.size = 22880 := actionChecks_parts.1

@[expose] def CMat : Type := Matrix (Fin 64) (Fin 64) (ZMod 3)

@[expose] def toCM (M : Matrix (Fin 64) (Fin 64) (ZMod 3)) : CMat := M

@[expose] def ofCM (M : CMat) : Matrix (Fin 64) (Fin 64) (ZMod 3) := M

theorem ofCM_toCM (M : Matrix (Fin 64) (Fin 64) (ZMod 3)) : ofCM (toCM M) = M := rfl

theorem ofCM_injective : Function.Injective ofCM := fun _ _ h => h

noncomputable instance conjAction : MulAction J CMat where
  smul g M := toCM (mat g * ofCM M * mat g⁻¹)
  one_smul M := by
    show toCM (mat 1 * ofCM M * mat 1⁻¹) = M
    rw [inv_one, mat_one, one_mul, mul_one]
    rfl
  mul_smul g h M := by
    show toCM (mat (g * h) * ofCM M * mat (g * h)⁻¹) =
      toCM (mat g * ofCM (toCM (mat h * ofCM M * mat h⁻¹)) * mat g⁻¹)
    rw [_root_.mul_inv_rev, mat_mul, mat_mul, ofCM_toCM]
    simp only [mul_assoc]

theorem ofCM_smul
    (g : J) (M : CMat) : ofCM (g • M) = mat g * ofCM M * mat g⁻¹ := rfl

theorem mat_a_inv : mat a⁻¹ = mA := by rw [a_inv]; rfl

theorem mat_b_inv : mat b⁻¹ = mB * mB := by rw [b_inv, mat_mul]; rfl

@[expose] noncomputable def matPt (k : ℕ) : CMat := toCM (toMatW orb.keys[k]!)

theorem ofCM_matPt (k : ℕ) : ofCM (matPt k) = toMatW orb.keys[k]! := rfl

theorem a_smul_matPt {i : ℕ} (hi : i < orb.keys.size) :
    a • matPt i = matPt (ap orb.alpha i) := by
  apply ofCM_injective
  rw [ofCM_smul, mat_a_inv, ofCM_matPt, ofCM_matPt, (conjFacts.alpha i hi).2, toMatW_wA]
  rfl

theorem b_smul_matPt {i : ℕ} (hi : i < orb.keys.size) :
    b • matPt i = matPt (ap orb.beta i) := by
  apply ofCM_injective
  rw [ofCM_smul, mat_b_inv, ofCM_matPt, ofCM_matPt, (conjFacts.beta i hi).2, toMatW_wB,
    toMatW_wBi]
  rfl

theorem matPt_inj
    {i j : ℕ} (hi : i < orb.keys.size) (hj : j < orb.keys.size)
    (h : matPt i = matPt j) : i = j :=
  conjFacts.inj i hi j hj (congrArg ofCM h)

theorem orbit_hyps :
    (∀ i < orb.keys.size, ap orb.alpha i < orb.keys.size ∧
      a • matPt i = matPt (ap orb.alpha i)) ∧
    (∀ i < orb.keys.size, ap orb.beta i < orb.keys.size ∧
      b • matPt i = matPt (ap orb.beta i)) :=
  ⟨fun i hi => ⟨(conjFacts.alpha i hi).1, a_smul_matPt hi⟩,
    fun i hi => ⟨(conjFacts.beta i hi).1, b_smul_matPt hi⟩⟩

theorem orbit_eq :
    MulAction.orbit J (matPt 0) = matPt '' Set.Iio orb.keys.size :=
  orbit_eq_image closure_ab conjFacts.size_pos matPt orbit_hyps.1 orbit_hyps.2
    (ap orb.par) (ap orb.lab) conjFacts.tree

@[expose] noncomputable def ptEquiv :
    Fin 22880 ≃ MulAction.orbit J (matPt 0) :=
  (Fin.castOrderIso orb_size.symm).toEquiv.trans
    (orbitEquiv closure_ab conjFacts.size_pos matPt (fun _ hi _ hj h => matPt_inj hi hj h)
      orbit_hyps.1 orbit_hyps.2 (ap orb.par) (ap orb.lab) conjFacts.tree)

theorem ptEquiv_apply
    (i : Fin 22880) : (ptEquiv i : CMat) = matPt i.val := rfl

noncomputable instance idxInst :
    MulAction J (Fin 22880) := ptEquiv.mulAction J

theorem smul_def
    (g : J) (i : Fin 22880) : g • i = ptEquiv.symm (g • ptEquiv i) := rfl

theorem ptEquiv_smul
    (g : J) (i : Fin 22880) : ptEquiv (g • i) = g • ptEquiv i := by
  rw [smul_def, Equiv.apply_symm_apply]

theorem matPt_smul (g : J) (i : Fin 22880) :
    matPt (g • i : Fin 22880).val = g • matPt i.val := by
  have := congrArg Subtype.val (ptEquiv_smul g i)
  rw [ptEquiv_apply] at this
  rw [this]
  rfl

theorem smul_eq_iff
    (g : J) (i j : Fin 22880) : g • i = j ↔ g • matPt i.val = matPt j.val := by
  constructor
  · rintro rfl; exact (matPt_smul g i).symm
  · intro h
    apply Fin.ext
    apply matPt_inj (by rw [orb_size]; exact (g • i).isLt) (by rw [orb_size]; exact j.isLt)
    rw [matPt_smul, h]

theorem idx_eq_iff
    {g : J} {i j : ℕ} (hi : i < 22880) (hj : j < 22880) :
    idx 22880 g i = j ↔ g • matPt i = matPt j := by
  rw [idx_of_lt g hi]
  constructor
  · intro h
    exact (smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).1 (Fin.ext h)
  · intro h
    exact congrArg Fin.val ((smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).2 h)

theorem rep_alpha : Rep 22880 orb.alpha a := by
  intro i hi
  have hi' : i < orb.keys.size := by rw [orb_size]; exact hi
  have hlt : ap orb.alpha i < 22880 := by rw [← orb_size]; exact (conjFacts.alpha i hi').1
  symm
  exact (idx_eq_iff hi hlt).2 (a_smul_matPt hi')

theorem rep_beta : Rep 22880 orb.beta b := by
  intro i hi
  have hi' : i < orb.keys.size := by rw [orb_size]; exact hi
  have hlt : ap orb.beta i < 22880 := by rw [← orb_size]; exact (conjFacts.beta i hi').1
  symm
  exact (idx_eq_iff hi hlt).2 (b_smul_matPt hi')

theorem commute_of_idx_fix
    {g : J} {r : ℕ} (hr : r < 22880) (h : idx 22880 g r = r) :
    mat g * toMatW orb.keys[r]! = toMatW orb.keys[r]! * mat g := by
  have e := congrArg ofCM ((idx_eq_iff hr hr).1 h)
  rw [ofCM_smul, ofCM_matPt] at e
  calc mat g * toMatW orb.keys[r]! = mat g * toMatW orb.keys[r]! * mat g⁻¹ * mat g := by
        rw [mul_assoc (mat g * toMatW orb.keys[r]!), ← mat_mul, inv_mul_cancel, mat_one,
          mul_one]
    _ = toMatW orb.keys[r]! * mat g := by rw [e]

private theorem zmod3_cases : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide

theorem sep
    (g : J) (hg : ∀ t < chainQ.size, idx 22880 g chainQ[t]! = chainQ[t]!) : g = 1 := by
  obtain ⟨-, -, -, -, hsep, hlt, -⟩ := actionChecks_parts
  obtain ⟨c, hc⟩ := scalar_of_sepOK hsep (mat g) (fun i hi => by
    have hi' : i < sepIdx.size := by simpa using hi
    have hr : sepIdx[i]! < 22880 := by
      rw [getElem!_pos sepIdx i hi']
      exact hlt _ (Array.getElem_mem hi')
    have e : (sepIdx.map fun r => toVM orb.keys[r]!)[i]! = toVM orb.keys[sepIdx[i]!]! := by
      rw [getElem!_pos _ i hi, Array.getElem_map, getElem!_pos sepIdx i hi']
    rw [e]
    exact commute_of_idx_fix hr (hg i hi'))
  have hunit : mat g * mat g⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  rcases zmod3_cases c with rfl | rfl | rfl
  · rw [hc, zero_smul, zero_mul] at hunit
    have := congrFun (congrFun hunit 0) 0
    simp at this
  · apply mat_injective
    rw [hc, one_smul, mat_one]
  · exfalso
    apply mat_ne_neg_one g
    rw [hc]
    ext i j
    simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> decide

theorem eq_one_of_fix_all
    {g : J} (h : ∀ i : Fin 22880, g • i = i) : g = 1 := by
  apply sep
  intro t ht
  have hQ : chainQ[t]! < 22880 := by
    have hlt := actionChecks_parts.2.2.2.2.2.1
    have ht' : t < sepIdx.size := ht
    show sepIdx[t]! < 22880
    rw [getElem!_pos sepIdx t ht']
    exact hlt _ (Array.getElem_mem ht')
  rw [idx_of_lt g hQ, h]

instance faithful : FaithfulSMul J (Fin 22880) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := eq_one_of_fix_all fun i => by rw [mul_smul, hgh, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

end CFSG.Sporadic.Suz
