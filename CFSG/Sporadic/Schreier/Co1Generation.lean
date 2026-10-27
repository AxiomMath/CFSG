module

public import CFSG.Sporadic.Schreier.Co1GenCheck
public import CFSG.Sporadic.Schreier.Co1Rigidity

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix
open scoped Pointwise
open CFSG.Sporadic.SmallF2 (rowsMatrix toVecD toVecD_xor toVecD_injective)
open CFSG.Sporadic.SmallF2.Native (vecMulN)

theorem card_GA : Nat.card GA = 4157776806543360000 := by
  have h := CFSG.Sporadic.SmallF2.card_lvl CFSG.Sporadic.Co1.co1Facts (i := 0) (Nat.zero_le _)
  rw [CFSG.Sporadic.SmallF2.lvl_zero CFSG.Sporadic.Co1.co1Facts, Subgroup.card_top] at h
  exact h.trans (by decide)

theorem extInit_rep :
    List.Forall₂ MRep Native.extInitRows extInit :=
  .cons (a_rep 0) (.cons (a_rep 1) (.cons (a_rep 2) (.cons (a_rep 3) (.cons (a_rep 4)
    (.cons (a_rep 5) (.cons (c_rep 0) (.cons (c_rep 1) (.cons (g_rep 2) (.cons rep_x .nil)))))))))

theorem gen_facts :
    Native.extDag.2.2 = true ∧ Native.extDag.1.length = 93 ∧
    ∀ i < 7, Native.towerB i < 2 ^ 24 ∧ Native.towerQ i < 2 ^ 24 ∧ Native.fixOK i = true ∧
      Native.treeOK (Native.towerQ i) (Native.towerJ i) (Native.towerB i) (Native.towerN i)
        (Native.towerTree i) = true := by
  have h := gen_check
  simp only [Native.genCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, and_assoc] at h
  exact h

theorem extL_rep :
    List.Forall₂ MRep Native.extDag.1 extL :=
  dag_rep extInit_rep Data.genDerivs gen_facts.1

theorem extL_mem (j : ℕ) : extL.getD j 1 ∈ extM := by
  refine getD_mem_of_forall (dagG_mem (fun g hg => ?_) Data.genDerivs) j
  exact Subgroup.subset_closure hg

theorem extM_le_GA : extM ≤ GA := by
  refine (Subgroup.closure_le _).mpr fun g hg => ?_
  simp only [extInit, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
  have hA : ∀ y ∈ A, y ∈ GA := fun y hy => A_le_GA hy
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hA _ (E_le_A (a_mem_E 0))
  · exact hA _ (E_le_A (a_mem_E 1))
  · exact hA _ (E_le_A (a_mem_E 2))
  · exact hA _ (E_le_A (a_mem_E 3))
  · exact hA _ (E_le_A (a_mem_E 4))
  · exact hA _ (E_le_A (a_mem_E 5))
  · exact hA _ (c_mem_A 0)
  · exact hA _ (c_mem_A 1)
  · exact hA _ r_mem_A
  · exact threeLocal_mem.1

theorem extM_le_closure : extM ≤ Subgroup.closure ((A : Set GL24) ∪ {ThreeLocal.x}) := by
  refine (Subgroup.closure_le _).mpr fun g hg => Subgroup.subset_closure ?_
  simp only [extInit, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (E_le_A (a_mem_E 0))
  · exact Or.inl (E_le_A (a_mem_E 1))
  · exact Or.inl (E_le_A (a_mem_E 2))
  · exact Or.inl (E_le_A (a_mem_E 3))
  · exact Or.inl (E_le_A (a_mem_E 4))
  · exact Or.inl (E_le_A (a_mem_E 5))
  · exact Or.inl (c_mem_A 0)
  · exact Or.inl (c_mem_A 1)
  · exact Or.inl r_mem_A
  · exact Or.inr rfl

@[expose, instance_reducible] def glAct : MulAction GL24 Vec24 where
  smul g v := (g : Mat24) *ᵥ v
  one_smul v := by
    show ((1 : GL24) : Mat24) *ᵥ v = v
    rw [Units.val_one, one_mulVec]
  mul_smul g h v := by
    show ((g * h : GL24) : Mat24) *ᵥ v = (g : Mat24) *ᵥ ((h : Mat24) *ᵥ v)
    rw [Units.val_mul, mulVec_mulVec]

attribute [local instance] glAct

theorem glAct_smul (g : GL24) (v : Vec24) : g • v = (g : Mat24) *ᵥ v := rfl

theorem extL_smul
    {j : ℕ} (hj : j < 93) (v : ℕ) :
    extL.getD j 1 • toVecD 24 v = toVecD 24 (vecMulN 24 (Native.extColsT.getD j #[]) v) := by
  have h := getD_rep extL_rep MRep.one j
  rw [glAct_smul, MRep.mulVec h, Native.extColsT, ofFn_getD _ _ hj]
  rfl

@[expose] def pairSet (q v : Vec24) : Set Vec24 := {v, v + q}

theorem vec_add_self (q : Vec24) : q + q = 0 := funext fun i => by
  show q i + q i = 0
  generalize q i = z
  revert z
  decide

theorem pairSet_add (q v : Vec24) : pairSet q (v + q) = pairSet q v := by
  rw [pairSet, pairSet, add_assoc, vec_add_self, add_zero, Set.pair_comm]

theorem smul_pairSet {g : GL24} {q : Vec24} (hq : g • q = q) (v : Vec24) :
    g • pairSet q v = pairSet q (g • v) := by
  rw [pairSet, Set.smul_set_insert, Set.smul_set_singleton, glAct_smul, glAct_smul, mulVec_add,
    ← glAct_smul g q, hq, pairSet]

theorem canon_cases (q v : ℕ) : Native.canon q v = v ∨ Native.canon q v = v ^^^ q := by
  unfold Native.canon
  rcases le_total v (v ^^^ q) with h | h
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right h)

theorem pairSet_canon (q v : ℕ) : pairSet (toVecD 24 q) (toVecD 24 (Native.canon q v)) =
    pairSet (toVecD 24 q) (toVecD 24 v) := by
  rcases canon_cases q v with h | h
  · rw [h]
  · rw [h, toVecD_xor, pairSet_add]

noncomputable def towerSet (i : ℕ) : Set Vec24 :=
  pairSet (toVecD 24 (Native.towerQ i)) (toVecD 24 (Native.towerB i))

noncomputable def chainH : ℕ → Subgroup GL24
  | 0 => extM
  | i + 1 => (MulAction.stabilizer (chainH i) (towerSet i)).map (chainH i).subtype

theorem mem_chainH_succ {i : ℕ} {g : GL24} :
    g ∈ chainH (i + 1) ↔ g ∈ chainH i ∧ g • towerSet i = towerSet i := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, hh⟩
  · rintro ⟨hg, hs⟩
    exact ⟨⟨g, hg⟩, hs, rfl⟩

theorem card_chainH (i : ℕ) : Nat.card (chainH i) =
    Nat.card (MulAction.orbit (chainH i) (towerSet i)) * Nat.card (chainH (i + 1)) := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (chainH i) (towerSet i)),
    Nat.card_prod, chainH, Subgroup.card_map_of_injective (chainH i).subtype_injective]

theorem extL_fix
    {i j : ℕ} (hi : i < 7) (hj : j ∈ Native.towerJ i) :
    j < 93 ∧ extL.getD j 1 • toVecD 24 (Native.towerQ i) = toVecD 24 (Native.towerQ i) ∧
      ∀ l < i, extL.getD j 1 • towerSet l = towerSet l := by
  have h := (gen_facts.2.2 i hi).2.2.1
  simp only [Native.fixOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.mem_range, Bool.or_eq_true, and_assoc] at h
  obtain ⟨hj93, hq, hl⟩ := h j hj
  refine ⟨hj93, by rw [extL_smul hj93, hq], fun l hl' => ?_⟩
  obtain ⟨hql, hbl⟩ := hl l hl'
  rw [towerSet, smul_pairSet (by rw [extL_smul hj93, hql]), extL_smul hj93]
  rcases hbl with hb | hb
  · rw [hb]
  · rw [hb, toVecD_xor, pairSet_add]

theorem extL_mem_chainH
    {i j : ℕ} (hi : i < 7) (hj : j ∈ Native.towerJ i) :
    extL.getD j 1 ∈ chainH i := by
  obtain ⟨-, -, hfix⟩ := extL_fix hi hj
  suffices ∀ k ≤ i, extL.getD j 1 ∈ chainH k from this i le_rfl
  intro k
  induction k with
  | zero => exact fun _ => extL_mem j
  | succ k ih =>
    intro hk
    exact mem_chainH_succ.mpr ⟨ih (by omega), hfix k (by omega)⟩

theorem strictSorted_pairwise :
    ∀ l : List ℕ, Native.strictSorted l = true → List.Pairwise (· < ·) l
  | [] => fun _ => List.Pairwise.nil
  | [a] => fun _ => List.pairwise_singleton _ a
  | a :: b :: r => fun h => by
    simp only [Native.strictSorted, Bool.and_eq_true, decide_eq_true_eq] at h
    have hp := strictSorted_pairwise (b :: r) h.2
    refine List.Pairwise.cons (fun z hz => ?_) hp
    rcases List.mem_cons.mp hz with rfl | hz
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons hp hz)

theorem treeOK_parts {q root n : ℕ} {gens : List ℕ} {t : Array (ℕ × ℕ × ℕ)}
    (h : Native.treeOK q gens root n t = true) :
    t.size = n ∧ (t.getD 0 (0, 0, 0)).1 = root ∧
    (∀ m < n, (t.getD m (0, 0, 0)).1 < 2 ^ 24 ∧
      Native.canon q (t.getD m (0, 0, 0)).1 = (t.getD m (0, 0, 0)).1 ∧
      (m = 0 ∨ (t.getD m (0, 0, 0)).2.1 < m ∧ (t.getD m (0, 0, 0)).2.2 ∈ gens ∧
        (t.getD m (0, 0, 0)).1 =
          Native.stepV q (t.getD m (0, 0, 0)).2.2 (t.getD (t.getD m (0, 0, 0)).2.1 (0, 0, 0)).1)) ∧
    (t.toList.map (·.1)).Nodup := by
  simp only [Native.treeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, List.contains_iff_mem, and_assoc] at h
  obtain ⟨hs, hr, hall, hsort⟩ := h
  exact ⟨hs, hr, hall, (List.mergeSort_perm _ _).nodup_iff.mp
    ((strictSorted_pairwise _ hsort).imp ne_of_lt)⟩

theorem tree_mem_orbit
    {i : ℕ} (hi : i < 7) : ∀ m < Native.towerN i,
    pairSet (toVecD 24 (Native.towerQ i)) (toVecD 24 ((Native.towerTree i).getD m (0, 0, 0)).1) ∈
      MulAction.orbit (chainH i) (towerSet i) := by
  obtain ⟨-, hroot, hall, -⟩ := treeOK_parts (gen_facts.2.2 i hi).2.2.2
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases (hall m hm).2.2 with rfl | ⟨hp, hg, he⟩
    · rw [hroot]
      exact MulAction.mem_orbit_iff.mpr ⟨1, one_smul _ _⟩
    · obtain ⟨g, hg'⟩ := MulAction.mem_orbit_iff.mp (ih _ hp (hp.trans hm))
      obtain ⟨hj93, hq, -⟩ := extL_fix hi hg
      refine MulAction.mem_orbit_iff.mpr ⟨⟨extL.getD _ 1, extL_mem_chainH hi hg⟩ * g, ?_⟩
      rw [mul_smul, hg', Subgroup.smul_def, smul_pairSet hq, extL_smul hj93, he, Native.stepV,
        pairSet_canon]

theorem pairSet_inj {q v w : ℕ} (hq : q < 2 ^ 24) (hv : v < 2 ^ 24) (hw : w < 2 ^ 24)
    (hcv : Native.canon q v = v) (hcw : Native.canon q w = w)
    (h : pairSet (toVecD 24 q) (toVecD 24 v) = pairSet (toVecD 24 q) (toVecD 24 w)) : v = w := by
  have hmem : toVecD 24 w ∈ pairSet (toVecD 24 q) (toVecD 24 v) := by
    rw [h]
    exact Set.mem_insert _ _
  rcases hmem with hwv | hwv
  · exact (toVecD_injective hw hv hwv).symm
  · rw [Set.mem_singleton_iff, ← toVecD_xor] at hwv
    have hxor : v ^^^ q < 2 ^ 24 := Nat.xor_lt_two_pow hv hq
    have hw' := toVecD_injective hw hxor hwv
    subst hw'
    unfold Native.canon at hcv hcw
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at hcw
    rw [← hcw, min_comm, hcv]

theorem towerN_le_card_orbit
    {i : ℕ} (hi : i < 7) :
    Native.towerN i ≤ Nat.card (MulAction.orbit (chainH i) (towerSet i)) := by
  obtain ⟨hsize, -, hall, hnodup⟩ := treeOK_parts (gen_facts.2.2 i hi).2.2.2
  obtain ⟨hb, hq, -⟩ := gen_facts.2.2 i hi
  have hmem := tree_mem_orbit hi
  have hget : ∀ m (hm : m < Native.towerN i), ((Native.towerTree i).getD m (0, 0, 0)).1 =
      ((Native.towerTree i).toList.map (·.1))[m]'(by
        rw [List.length_map, Array.length_toList, hsize]; exact hm) := by
    intro m hm
    rw [List.getElem_map, Array.getElem_toList, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (hsize ▸ hm), Option.getD_some]
  have hinj : Function.Injective fun m : Fin (Native.towerN i) =>
      (⟨_, hmem m.val m.isLt⟩ : MulAction.orbit (chainH i) (towerSet i)) := by
    intro m m' hmm
    have hpair := congrArg Subtype.val hmm
    have hv := pairSet_inj hq (hall m m.isLt).1 (hall m' m'.isLt).1 (hall m m.isLt).2.1
      (hall m' m'.isLt).2.1 hpair
    rw [hget m m.isLt, hget m' m'.isLt] at hv
    exact Fin.ext ((hnodup.getElem_inj_iff).mp hv)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem prod_towerN : ∏ i ∈ Finset.range 7, Native.towerN i = 4157776806543360000 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Native.towerN, Data.towerSizes]
  rfl

theorem card_extM_ge :
    4157776806543360000 ≤ Nat.card extM := by
  have key : ∀ k ≤ 7, (∏ i ∈ Finset.range k, Native.towerN i) * Nat.card (chainH k) ≤
      Nat.card (chainH 0) := by
    intro k
    induction k with
    | zero => intro _; rw [Finset.prod_range_zero, one_mul]
    | succ k ih =>
      intro hk
      refine le_trans ?_ (ih (by omega))
      rw [Finset.prod_range_succ, mul_assoc, card_chainH k]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (towerN_le_card_orbit (by omega)))
  have h7 := key 7 le_rfl
  rw [prod_towerN] at h7
  exact le_trans (Nat.le_mul_of_pos_right _ Nat.card_pos) h7

theorem local_enlargement_generation :
    Subgroup.closure ((A : Set GL24) ∪ {ThreeLocal.x}) = GA ∧
      Nat.card extM = 4157776806543360000 ∧ extM = GA := by
  have hM : extM = GA :=
    Subgroup.eq_of_le_of_card_ge extM_le_GA (by rw [card_GA]; exact card_extM_ge)
  refine ⟨le_antisymm ((Subgroup.closure_le _).mpr fun g hg => ?_) (hM ▸ extM_le_closure),
    by rw [hM, card_GA], hM⟩
  rcases hg with hg | hg
  · exact A_le_GA hg
  · rw [Set.mem_singleton_iff.mp hg]
    exact threeLocal_mem.1

end CFSG.Sporadic.Co1Schreier
