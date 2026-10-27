
module

public import CFSG.Sporadic.Fi23.ClassBase
import all CFSG.Sporadic.Fi23.ClassBase

public import CFSG.Sporadic.Fi23.Setup
public import CFSG.Sporadic.Th.OrbitSpec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Fi23

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem toMatW_matA_sq : toMatW 253 matA * toMatW 253 matA = 1 := by
  rw [toMatW_matA]; exact matrixFacts.A_sq

theorem toMatW_matB_cube : toMatW 253 matB ^ 3 = 1 := by
  rw [toMatW_matB, pow_three]; exact matrixFacts.B_inv

theorem toMatW_matBi_cube : toMatW 253 matBi ^ 3 = 1 := by
  rw [toMatW_matBi, ← sq, ← pow_mul, mul_comm, pow_mul, ← toMatW_matB, toMatW_matB_cube, one_pow]

theorem conjFacts : WConjFacts 253 matD matA matA matB matBi orb :=
  conjOrbitOKW_facts (by norm_num) (by norm_num) matA_size rowsWF_matA rowsWF_matA matB_size
    rowsWF_matB rowsWF_matBi toMatW_matA_sq toMatW_matA_sq toMatW_matB_cube toMatW_matBi_cube
    certificate_parts.2.1

theorem actionChecks_eq :
    actionChecks orb 3 = true := certificate_parts.2.2.1

structure ActionFacts : Prop where
  keys_size : orb.keys.size = 31671
  alpha_size : orb.alpha.size = 31671
  beta_size : orb.beta.size = 31671
  alpha_invo : invoOK 31671 orb.alpha = true
  beta_inv : invOK 31671 orb.beta (invT 31671 orb.beta) = true
  sep : sepOK 253 (chainQ.map fun r => toVM orb.keys[r]!) sepTerms sepVec sepK sepP sepTinv
    sepTree = true
  q_lt : chainQ.all (· < 31671) = true
  slp_ok : slpOK chainWords = true
  slp_pure : slpPure chainWords = true
  words_size : 2 ≤ chainWords.size
  word0 : chainWords[0]! = [1]
  word1 : chainWords[1]! = pairWord
  chain : CFSG.Perm.Native.chainOK 31671 letters chainBase chainQ chainQb trees 3 = true
  sizes : CFSG.Perm.Native.orbitSizes trees = [31671, 3510, 25344, 288, 1260, 4]
  sift_b : CFSG.Perm.Native.sift trees letters chainQb chainQ 0 (apT orb.beta chainQ) = true
  tree2 : CFSG.Perm.Native.treeOK 31671 subRoot T2 letters lv1 = true
  T2_size : T2.pts.size = 28160
  cover : allIn 0 31671 (fun p => p == 0 || inTreeB trees[1]! p || inTreeB T2 p) = true
  y_pow : isIdT (powT 31671 17 tabY) = true
  y_ne : isIdT tabY = false
  ay_pow : isIdT (powT 31671 23 tabAY) = true
  ay_ne : isIdT tabAY = false

theorem actionFacts : ActionFacts := by
  have h := actionChecks_eq
  unfold actionChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
    h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22⟩

theorem orb_size : orb.keys.size = 31671 := actionFacts.keys_size

@[expose] noncomputable def labG
    (l : ℕ) : J := if l = 1 then a else b

@[expose] noncomputable def conjPt (k : ℕ) : J :=
  if _h : 0 < k ∧ ap orb.par k < k then
    labG (ap orb.lab k) * conjPt (ap orb.par k) * (labG (ap orb.lab k))⁻¹
  else d
termination_by k

theorem mat_a_inv :
    mat a⁻¹ = toMatW 253 matA := by rw [a_inv, mat_a, toMatW_matA]

theorem mat_conj_a (x : J) :
    mat (a * x * a⁻¹) = toMatW 253 matA * mat x * toMatW 253 matA := by
  rw [mat_mul, mat_mul, mat_a_inv, mat_a, toMatW_matA]

theorem mat_conj_b (x : J) :
    mat (b * x * b⁻¹) = toMatW 253 matB * mat x * toMatW 253 matBi := by
  rw [mat_mul, mat_mul, mat_b_inv, mat_b, toMatW_matB]

theorem conjPt_mat :
    ∀ k < orb.keys.size, mat (conjPt k) = toMatW 253 orb.keys[k]! := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [conjPt.eq_def]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [lt_irrefl, false_and, dite_false]
      rw [conjFacts.root, mat_d]
    · obtain ⟨hpar, hcase⟩ := conjFacts.tree k hk hk0
      rw [dite_eq_left ⟨hk0, hpar⟩]
      have hp := ih _ hpar (lt_trans hpar hk)
      rcases hcase with ⟨hl, ha⟩ | ⟨hl, hb⟩
      · have : labG (ap orb.lab k) = a := by simp [labG, hl]
        rw [this, mat_conj_a, hp, ← (conjFacts.alpha _ (lt_trans hpar hk)).2, ha]
      · have : labG (ap orb.lab k) = b := by simp [labG, hl]
        rw [this, mat_conj_b, hp, ← (conjFacts.beta _ (lt_trans hpar hk)).2, hb]

theorem conjPt_zero : conjPt 0 = d := by
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
    MulAction.orbit (ConjAct J) d = conjPt '' Set.Iio orb.keys.size := by
  rw [← conjPt_zero]
  exact orbit_eq_image closure_conjAct conjFacts.size_pos conjPt orbit_hyps.1 orbit_hyps.2
    (ap orb.par) (ap orb.lab) conjFacts.tree

@[expose] noncomputable def ptEquiv :
    Fin 31671 ≃ MulAction.orbit (ConjAct J) d :=
  (Fin.castOrderIso orb_size.symm).toEquiv.trans
    ((orbitEquiv closure_conjAct conjFacts.size_pos conjPt
      (fun i hi j hj h => conjPt_inj hi hj h) orbit_hyps.1 orbit_hyps.2 (ap orb.par) (ap orb.lab)
      conjFacts.tree).trans (Equiv.subtypeEquivRight fun x => by rw [conjPt_zero]))

theorem ptEquiv_apply
    (i : Fin 31671) : (ptEquiv i : J) = conjPt i.val := rfl

noncomputable abbrev conjIdx :
    MulAction (ConjAct J) (Fin 31671) := ptEquiv.mulAction (ConjAct J)

noncomputable instance idxInst : MulAction J (Fin 31671) :=
  letI := conjIdx
  MulAction.compHom (Fin 31671) (@ConjAct.toConjAct J _).toMonoidHom

theorem smul_def (g : J) (i : Fin 31671) :
    g • i = ptEquiv.symm (ConjAct.toConjAct g • ptEquiv i) := rfl

theorem ptEquiv_smul (g : J) (i : Fin 31671) :
    ptEquiv (g • i) = ConjAct.toConjAct g • ptEquiv i := by
  rw [smul_def, Equiv.apply_symm_apply]

theorem conjPt_smul (g : J) (i : Fin 31671) :
    conjPt (g • i : Fin 31671).val = g * conjPt i.val * g⁻¹ := by
  have := congrArg Subtype.val (ptEquiv_smul g i)
  rw [ptEquiv_apply] at this
  rw [this]
  show (ConjAct.toConjAct g • (ptEquiv i : J)) = _
  rw [toConjAct_smul_eq, ptEquiv_apply]

theorem smul_eq_iff (g : J) (i j : Fin 31671) :
    g • i = j ↔ g * conjPt i.val * g⁻¹ = conjPt j.val := by
  constructor
  · rintro rfl; exact (conjPt_smul g i).symm
  · intro h
    apply Fin.ext
    apply conjPt_inj (by rw [orb_size]; exact (g • i).isLt) (by rw [orb_size]; exact j.isLt)
    rw [conjPt_smul, h]

theorem idx_eq_iff
    {g : J} {i j : ℕ} (hi : i < 31671) (hj : j < 31671) :
    idx 31671 g i = j ↔ g * conjPt i * g⁻¹ = conjPt j := by
  rw [idx_of_lt g hi]
  constructor
  · intro h
    exact (smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).1 (Fin.ext h)
  · intro h
    exact congrArg Fin.val ((smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).2 h)

theorem rep_alpha : Rep 31671 orb.alpha a := by
  intro i hi
  have hi' : i < orb.keys.size := by rw [orb_size]; exact hi
  have hlt : ap orb.alpha i < 31671 := by rw [← orb_size]; exact (conjFacts.alpha i hi').1
  symm
  exact (idx_eq_iff hi hlt).2 (conj_a_conjPt hi')

theorem rep_beta : Rep 31671 orb.beta b := by
  intro i hi
  have hi' : i < orb.keys.size := by rw [orb_size]; exact hi
  have hlt : ap orb.beta i < 31671 := by rw [← orb_size]; exact (conjFacts.beta i hi').1
  symm
  exact (idx_eq_iff hi hlt).2 (conj_b_conjPt hi')

end CFSG.Sporadic.Fi23
