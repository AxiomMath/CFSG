module

public import CFSG.Sporadic.Fi22.Setup
public import CFSG.Sporadic.Th.OrbitSpec

public section

namespace CFSG.Sporadic.Fi22

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem conjFacts : ConjFacts 77 matA matA matB matBi orb :=
  conjOrbitOK_facts matA_size rowsWF_matA rowsWF_matA matB_size rowsWF_matB rowsWF_matBi
    certificate_parts.2.1

theorem actionChecks_parts :
    orb.keys.size = 3510 ∧ orb.alpha.size = 3510 ∧
    orb.beta.size = 3510 ∧ invoOK 3510 orb.alpha = true ∧
    invOK 3510 orb.beta (invT 3510 orb.beta) = true ∧
    sepOK 77 (sepIdx.map fun r => orb.keys[r]!) sepTerms sepVec sepK sepP sepTinv sepTree = true ∧
    (∀ r ∈ sepIdx, r < 3510) ∧
    CFSG.Perm.Native.chainOK 3510 (chainLetters orb) chainBase chainQ chainQb
      (CFSG.Perm.Native.chainTrees 3510 (chainLetters orb) chainBase) 3 = true ∧
    CFSG.Perm.Native.orbitSizes (CFSG.Perm.Native.chainTrees 3510 (chainLetters orb) chainBase) =
      [3510, 2816, 1680, 108, 36] ∧
    CFSG.Perm.Native.treeOK 3510 subRoot
      (CFSG.Perm.Native.treeBFS 3510 subRoot (chainLetters orb)
        (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1))
      (chainLetters orb) (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1) = true ∧
    (CFSG.Perm.Native.treeBFS 3510 subRoot (chainLetters orb)
      (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1)).pts.size = 693 ∧
    ∀ p < 3510, p = 0 ∨
      (ap (CFSG.Perm.Native.chainTrees 3510 (chainLetters orb) chainBase)[1]!.pos p <
        (CFSG.Perm.Native.chainTrees 3510 (chainLetters orb) chainBase)[1]!.pts.size ∧
       ap (CFSG.Perm.Native.chainTrees 3510 (chainLetters orb) chainBase)[1]!.pts
        (ap (CFSG.Perm.Native.chainTrees 3510 (chainLetters orb) chainBase)[1]!.pos p) = p) ∨
      (ap (CFSG.Perm.Native.treeBFS 3510 subRoot (chainLetters orb)
        (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1)).pos p < 693 ∧
       ap (CFSG.Perm.Native.treeBFS 3510 subRoot (chainLetters orb)
        (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1)).pts
        (ap (CFSG.Perm.Native.treeBFS 3510 subRoot (chainLetters orb)
          (CFSG.Perm.Native.levelLetters (chainLetters orb) chainBase 1)).pos p) = p) := by
  have h := certificate_parts.2.2.1
  unfold actionChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun r hr => ?_, h8, h9, h10, h11, fun p hp => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hr
    exact h7 i hi
  · have := (allIn_eq_true.1 h12) p (Nat.zero_le _) hp
    simpa only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, or_assoc]
      using this

theorem orb_size : orb.keys.size = 3510 := actionChecks_parts.1

@[expose] noncomputable def labG
    (l : ℕ) : J := if l = 1 then a else b

@[expose] noncomputable def conjPt (k : ℕ) : J :=
  if _h : 0 < k ∧ ap orb.par k < k then
    labG (ap orb.lab k) * conjPt (ap orb.par k) * (labG (ap orb.lab k))⁻¹
  else a
termination_by k

noncomputable abbrev mat
    (g : J) : Matrix (Fin 77) (Fin 77) (ZMod 3) :=
  ((g : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3))

theorem mat_mul (g h : J) : mat (g * h) = mat g * mat h := rfl

theorem mat_injective : Function.Injective mat := by
  intro g h e
  exact Subtype.ext (Units.ext e)

theorem mat_a : mat a = toMat 77 matA := by rw [toMat_matA]; rfl

theorem mat_b : mat b = toMat 77 matB := by rw [toMat_matB]; rfl

theorem mat_a_inv : mat a⁻¹ = toMat 77 matA := by rw [a_inv, mat_a]

theorem mat_b_inv : mat b⁻¹ = toMat 77 matBi := b_inv_val

theorem mat_conj_a
    (x : J) : mat (a * x * a⁻¹) = toMat 77 matA * mat x * toMat 77 matA := by
  rw [mat_mul, mat_mul, mat_a_inv, mat_a]

theorem mat_conj_b
    (x : J) : mat (b * x * b⁻¹) = toMat 77 matB * mat x * toMat 77 matBi := by
  rw [mat_mul, mat_mul, mat_b_inv, mat_b]

theorem conjPt_mat :
    ∀ k < orb.keys.size, mat (conjPt k) = toMat 77 orb.keys[k]! := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [conjPt.eq_def]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [lt_irrefl, false_and, dite_false]
      rw [conjFacts.root, mat_a]
    · obtain ⟨hpar, hcase⟩ := conjFacts.tree k hk hk0
      rw [dite_eq_left ⟨hk0, hpar⟩]
      have hp := ih _ hpar (lt_trans hpar hk)
      rcases hcase with ⟨hl, ha⟩ | ⟨hl, hb⟩
      · have : labG (ap orb.lab k) = a := by simp [labG, hl]
        rw [this, mat_conj_a, hp, ← (conjFacts.alpha _ (lt_trans hpar hk)).2, ha]
      · have : labG (ap orb.lab k) = b := by simp [labG, hl]
        rw [this, mat_conj_b, hp, ← (conjFacts.beta _ (lt_trans hpar hk)).2, hb]

theorem conjPt_zero : conjPt 0 = a := by
  rw [conjPt.eq_def]; simp

theorem conj_a_conjPt {i : ℕ} (hi : i < orb.keys.size) :
    a * conjPt i * a⁻¹ = conjPt (ap orb.alpha i) := by
  apply mat_injective
  rw [mat_conj_a, conjPt_mat i hi, conjPt_mat _ (conjFacts.alpha i hi).1,
    (conjFacts.alpha i hi).2]

theorem conj_b_conjPt {i : ℕ} (hi : i < orb.keys.size) :
    b * conjPt i * b⁻¹ = conjPt (ap orb.beta i) := by
  apply mat_injective
  rw [mat_conj_b, conjPt_mat i hi, conjPt_mat _ (conjFacts.beta i hi).1, (conjFacts.beta i hi).2]

theorem conjPt_inj
    {i j : ℕ} (hi : i < orb.keys.size) (hj : j < orb.keys.size)
    (h : conjPt i = conjPt j) : i = j := by
  apply conjFacts.inj i hi j hj
  rw [← conjPt_mat i hi, ← conjPt_mat j hj, h]

open ConjAct in
theorem closure_conjAct :
    Subgroup.closure ({toConjAct a, toConjAct b} : Set (ConjAct J)) = ⊤ := by
  have key : ∀ g ∈ Subgroup.closure ({a, b} : Set J),
      toConjAct g ∈ Subgroup.closure ({toConjAct a, toConjAct b} : Set (ConjAct J)) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul y z _ _ hy hz => rw [map_mul]; exact Subgroup.mul_mem _ hy hz
    | inv y _ hy => rw [map_inv]; exact Subgroup.inv_mem _ hy
  rw [eq_top_iff]
  intro x _
  have := key (ofConjAct x) (by rw [closure_ab]; trivial)
  rwa [toConjAct_ofConjAct] at this

open ConjAct in
theorem toConjAct_smul_eq
    (g x : J) : toConjAct g • x = g * x * g⁻¹ := by
  rw [ConjAct.smul_def, ofConjAct_toConjAct]

theorem orbit_hyps :
    (∀ i < orb.keys.size, ap orb.alpha i < orb.keys.size ∧
      ConjAct.toConjAct a • conjPt i = conjPt (ap orb.alpha i)) ∧
    (∀ i < orb.keys.size, ap orb.beta i < orb.keys.size ∧
      ConjAct.toConjAct b • conjPt i = conjPt (ap orb.beta i)) := by
  refine ⟨fun i hi => ⟨(conjFacts.alpha i hi).1, ?_⟩, fun i hi => ⟨(conjFacts.beta i hi).1, ?_⟩⟩
  · rw [toConjAct_smul_eq, conj_a_conjPt hi]
  · rw [toConjAct_smul_eq, conj_b_conjPt hi]

theorem orbit_eq :
    MulAction.orbit (ConjAct J) a = conjPt '' Set.Iio orb.keys.size := by
  rw [← conjPt_zero]
  exact orbit_eq_image closure_conjAct conjFacts.size_pos conjPt orbit_hyps.1 orbit_hyps.2
    (ap orb.par) (ap orb.lab) conjFacts.tree

@[expose] noncomputable def ptEquiv :
    Fin 3510 ≃ MulAction.orbit (ConjAct J) a :=
  (Fin.castOrderIso orb_size.symm).toEquiv.trans
    ((orbitEquiv closure_conjAct conjFacts.size_pos conjPt
      (fun i hi j hj h => conjPt_inj hi hj h) orbit_hyps.1 orbit_hyps.2 (ap orb.par) (ap orb.lab)
      conjFacts.tree).trans (Equiv.subtypeEquivRight fun x => by rw [conjPt_zero]))

theorem ptEquiv_apply
    (i : Fin 3510) : (ptEquiv i : J) = conjPt i.val := rfl

noncomputable abbrev conjIdx :
    MulAction (ConjAct J) (Fin 3510) := ptEquiv.mulAction (ConjAct J)

noncomputable instance idxInst : MulAction J (Fin 3510) :=
  letI := conjIdx
  MulAction.compHom (Fin 3510) (@ConjAct.toConjAct J _).toMonoidHom

theorem smul_def (g : J) (i : Fin 3510) :
    g • i = ptEquiv.symm (ConjAct.toConjAct g • ptEquiv i) := rfl

theorem ptEquiv_smul (g : J) (i : Fin 3510) :
    ptEquiv (g • i) = ConjAct.toConjAct g • ptEquiv i := by
  rw [smul_def, Equiv.apply_symm_apply]

theorem conjPt_smul (g : J) (i : Fin 3510) :
    conjPt (g • i : Fin 3510).val = g * conjPt i.val * g⁻¹ := by
  have := congrArg Subtype.val (ptEquiv_smul g i)
  rw [ptEquiv_apply] at this
  rw [this]
  show (ConjAct.toConjAct g • (ptEquiv i : J)) = _
  rw [toConjAct_smul_eq, ptEquiv_apply]

theorem smul_eq_iff (g : J) (i j : Fin 3510) :
    g • i = j ↔ g * conjPt i.val * g⁻¹ = conjPt j.val := by
  constructor
  · rintro rfl; exact (conjPt_smul g i).symm
  · intro h
    apply Fin.ext
    apply conjPt_inj (by rw [orb_size]; exact (g • i).isLt) (by rw [orb_size]; exact j.isLt)
    rw [conjPt_smul, h]

theorem idx_eq_iff
    {g : J} {i j : ℕ} (hi : i < 3510) (hj : j < 3510) :
    idx 3510 g i = j ↔ g * conjPt i * g⁻¹ = conjPt j := by
  rw [idx_of_lt g hi]
  constructor
  · intro h
    have := (smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).1 (Fin.ext h)
    exact this
  · intro h
    exact congrArg Fin.val ((smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).2 h)

theorem rep_alpha : Rep 3510 orb.alpha a := by
  intro i hi
  have hi' : i < orb.keys.size := by rw [orb_size]; exact hi
  have hlt : ap orb.alpha i < 3510 := by rw [← orb_size]; exact (conjFacts.alpha i hi').1
  symm
  exact (idx_eq_iff hi hlt).2 (conj_a_conjPt hi')

theorem rep_beta : Rep 3510 orb.beta b := by
  intro i hi
  have hi' : i < orb.keys.size := by rw [orb_size]; exact hi
  have hlt : ap orb.beta i < 3510 := by rw [← orb_size]; exact (conjFacts.beta i hi').1
  symm
  exact (idx_eq_iff hi hlt).2 (conj_b_conjPt hi')

end CFSG.Sporadic.Fi22
