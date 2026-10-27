module

public import CFSG.Sporadic.McL.Setup
public import CFSG.Sporadic.Th.OrbitSpec

public section

namespace CFSG.Sporadic.McL

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.VecOrbit
  CFSG.Sporadic.VecOrbit.Native Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable instance vecAction :
    MulAction J (Fin 21 → ZMod 3) where
  smul g v := (mat g).mulVec v
  one_smul v := Matrix.one_mulVec v
  mul_smul g h v := (Matrix.mulVec_mulVec v (mat g) (mat h)).symm

theorem smul_vec
    (g : J) (v : Fin 21 → ZMod 3) : g • v = (mat g).mulVec v := rfl

theorem vecFacts :
    VecFacts 21 matA matB orb := vecOrbitOK_facts certificate_parts.2.1

theorem actionChecks_parts :
    orb.pts.size = 275 ∧ orb.alpha.size = 275 ∧
    orb.beta.size = 275 ∧ invoOK 275 orb.alpha = true ∧
    invOK 275 orb.beta (invT 275 orb.beta) = true ∧
    chainQ.size = 21 ∧ (∀ r ∈ chainQ, r < 275) ∧
    basisOK 21 (chainQ.map fun r => orb.pts[r]!) basisTinv = true ∧
    CFSG.Perm.Native.chainOK 275 (chainLetters orb) chainBase chainQ chainQb
      (CFSG.Perm.Native.chainTrees 275 (chainLetters orb) chainBase) 3 = true ∧
    CFSG.Perm.Native.orbitSizes (CFSG.Perm.Native.chainTrees 275 (chainLetters orb) chainBase) =
      [275, 162, 56, 30, 4, 3] ∧
    CFSG.Perm.Native.treeOK 275 subRoot
      (CFSG.Perm.Native.treeBFS 275 subRoot (chainLetters orb)
        (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1))
      (chainLetters orb) (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1) = true ∧
    (CFSG.Perm.Native.treeBFS 275 subRoot (chainLetters orb)
      (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1)).pts.size = 112 ∧
    ∀ p < 275, p = 0 ∨
      (ap (CFSG.Perm.Native.chainTrees 275 (chainLetters orb) chainBase)[1]!.pos p <
        (CFSG.Perm.Native.chainTrees 275 (chainLetters orb) chainBase)[1]!.pts.size ∧
       ap (CFSG.Perm.Native.chainTrees 275 (chainLetters orb) chainBase)[1]!.pts
        (ap (CFSG.Perm.Native.chainTrees 275 (chainLetters orb) chainBase)[1]!.pos p) = p) ∨
      (ap (CFSG.Perm.Native.treeBFS 275 subRoot (chainLetters orb)
        (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1)).pos p < 112 ∧
       ap (CFSG.Perm.Native.treeBFS 275 subRoot (chainLetters orb)
        (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1)).pts
        (ap (CFSG.Perm.Native.treeBFS 275 subRoot (chainLetters orb)
          (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1)).pos p) = p) := by
  have h := certificate_parts.2.2
  unfold actionChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun r hr => ?_, h8, h9, h10, h11, h12, fun p hp => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hr
    exact h7 i hi
  · have := (allIn_eq_true.1 h13) p (Nat.zero_le _) hp
    simpa only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, or_assoc]
      using this

theorem orb_size : orb.pts.size = 275 := actionChecks_parts.1

@[expose] noncomputable def vecPt (k : ℕ) : Fin 21 → ZMod 3 := vecOf 21 orb.pts[k]!

theorem a_smul_vecPt
    {i : ℕ} (hi : i < orb.pts.size) : a • vecPt i = vecPt (ap orb.alpha i) := by
  rw [smul_vec, mat_a, vecPt, vecPt, (vecFacts.alpha i hi).2]

theorem b_smul_vecPt
    {i : ℕ} (hi : i < orb.pts.size) : b • vecPt i = vecPt (ap orb.beta i) := by
  rw [smul_vec, mat_b, vecPt, vecPt, (vecFacts.beta i hi).2]

theorem vecPt_inj
    {i j : ℕ} (hi : i < orb.pts.size) (hj : j < orb.pts.size)
    (h : vecPt i = vecPt j) : i = j :=
  vecFacts.inj i hi j hj h

theorem orbit_hyps :
    (∀ i < orb.pts.size, ap orb.alpha i < orb.pts.size ∧ a • vecPt i = vecPt (ap orb.alpha i)) ∧
    (∀ i < orb.pts.size, ap orb.beta i < orb.pts.size ∧ b • vecPt i = vecPt (ap orb.beta i)) :=
  ⟨fun i hi => ⟨(vecFacts.alpha i hi).1, a_smul_vecPt hi⟩,
    fun i hi => ⟨(vecFacts.beta i hi).1, b_smul_vecPt hi⟩⟩

theorem orbit_eq :
    MulAction.orbit J (vecPt 0) = vecPt '' Set.Iio orb.pts.size :=
  orbit_eq_image closure_ab vecFacts.size_pos vecPt orbit_hyps.1 orbit_hyps.2
    (ap orb.par) (ap orb.lab) vecFacts.tree

@[expose] noncomputable def ptEquiv :
    Fin 275 ≃ MulAction.orbit J (vecPt 0) :=
  (Fin.castOrderIso orb_size.symm).toEquiv.trans
    (orbitEquiv closure_ab vecFacts.size_pos vecPt (fun _ hi _ hj h => vecPt_inj hi hj h)
      orbit_hyps.1 orbit_hyps.2 (ap orb.par) (ap orb.lab) vecFacts.tree)

theorem ptEquiv_apply
    (i : Fin 275) : (ptEquiv i : Fin 21 → ZMod 3) = vecPt i.val := rfl

noncomputable instance idxInst :
    MulAction J (Fin 275) := ptEquiv.mulAction J

theorem smul_def
    (g : J) (i : Fin 275) : g • i = ptEquiv.symm (g • ptEquiv i) := rfl

theorem ptEquiv_smul
    (g : J) (i : Fin 275) : ptEquiv (g • i) = g • ptEquiv i := by
  rw [smul_def, Equiv.apply_symm_apply]

theorem vecPt_smul
    (g : J) (i : Fin 275) : vecPt (g • i : Fin 275).val = g • vecPt i.val := by
  have := congrArg Subtype.val (ptEquiv_smul g i)
  rw [ptEquiv_apply] at this
  rw [this]
  rfl

theorem smul_eq_iff
    (g : J) (i j : Fin 275) : g • i = j ↔ g • vecPt i.val = vecPt j.val := by
  constructor
  · rintro rfl; exact (vecPt_smul g i).symm
  · intro h
    apply Fin.ext
    apply vecPt_inj (by rw [orb_size]; exact (g • i).isLt) (by rw [orb_size]; exact j.isLt)
    rw [vecPt_smul, h]

theorem idx_eq_iff {g : J} {i j : ℕ} (hi : i < 275) (hj : j < 275) :
    idx 275 g i = j ↔ g • vecPt i = vecPt j := by
  rw [idx_of_lt g hi]
  constructor
  · intro h
    exact (smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).1 (Fin.ext h)
  · intro h
    exact congrArg Fin.val ((smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).2 h)

theorem rep_alpha : Rep 275 orb.alpha a := by
  intro i hi
  have hi' : i < orb.pts.size := by rw [orb_size]; exact hi
  have hlt : ap orb.alpha i < 275 := by rw [← orb_size]; exact (vecFacts.alpha i hi').1
  symm
  exact (idx_eq_iff hi hlt).2 (a_smul_vecPt hi')

theorem rep_beta : Rep 275 orb.beta b := by
  intro i hi
  have hi' : i < orb.pts.size := by rw [orb_size]; exact hi
  have hlt : ap orb.beta i < 275 := by rw [← orb_size]; exact (vecFacts.beta i hi').1
  symm
  exact (idx_eq_iff hi hlt).2 (b_smul_vecPt hi')

theorem sep
    (g : J) (hg : ∀ t < chainQ.size, idx 275 g chainQ[t]! = chainQ[t]!) : g = 1 := by
  obtain ⟨-, -, -, -, -, hQs, hQlt, hbasis, -⟩ := actionChecks_parts
  have hm : mat g = 1 := by
    refine eq_one_of_basisOK hbasis (mat g) fun i hi => ?_
    have hi' : i < chainQ.size := by rw [hQs]; exact hi
    have hQi : chainQ[i]! < 275 := by
      rw [getElem!_pos chainQ i hi']
      exact hQlt _ (Array.getElem_mem hi')
    have e : (chainQ.map fun r => orb.pts[r]!)[i]! = orb.pts[chainQ[i]!]! := by
      rw [getElem!_pos _ i (by simpa using hi'), Array.getElem_map, getElem!_pos chainQ i hi']
    rw [e]
    have := (idx_eq_iff hQi hQi).1 (hg i hi')
    exact this
  apply mat_injective
  rw [hm, mat_one]

theorem eq_one_of_fix_all
    {g : J} (h : ∀ i : Fin 275, g • i = i) : g = 1 := by
  apply sep
  intro t ht
  have hQ : chainQ[t]! < 275 := by
    rw [getElem!_pos chainQ t ht]
    exact actionChecks_parts.2.2.2.2.2.2.1 _ (Array.getElem_mem ht)
  rw [idx_of_lt g hQ, h]

instance faithful : FaithfulSMul J (Fin 275) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := eq_one_of_fix_all fun i => by rw [mul_smul, hgh, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

end CFSG.Sporadic.McL
