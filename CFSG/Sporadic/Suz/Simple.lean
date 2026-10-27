module

public import CFSG.Sporadic.Suz.Class
public import CFSG.Perm.ChainSpec

public section

namespace CFSG.Sporadic.Suz

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Blueprint

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def genG (z : ℤ) : J :=
  if z = 1 then a else if z = -1 then a⁻¹ else if z = 2 then b else b⁻¹

theorem rep_gen (z : ℤ) : Rep 22880 (genTables orb z) (genG z) := by
  unfold genTables genG
  by_cases h1 : z = 1
  · subst h1; simp only [true_or, ite_true]; exact rep_alpha
  · by_cases h2 : z = -1
    · subst h2
      simp only [or_true, ite_true, show (-1 : ℤ) ≠ 1 by decide, ite_false, a_inv]
      exact rep_alpha
    · by_cases h3 : z = 2
      · subst h3
        simp only [show (2 : ℤ) ≠ 1 by decide, show (2 : ℤ) ≠ -1 by decide, or_self, ite_false,
          ite_true]
        exact rep_beta
      · simp only [h1, h2, h3, or_self, ite_false]
        exact Rep.inv_of_invOK rep_beta actionChecks_parts.2.2.2.1

@[expose] noncomputable def gs
    (j : ℕ) : J := wordG genG chainWords[j]!

theorem chainLetters_size : (chainLetters orb).size = 2 * chainWords.size := by
  unfold chainLetters buildLetters; simp

theorem chainLetters_even {j : ℕ} (hj : j < chainWords.size) :
    (chainLetters orb)[2 * j]! = wordT 22880 (genTables orb) chainWords[j]! := by
  unfold chainLetters buildLetters
  rw [getElem!_pos _ (2 * j) (by simp; omega), Array.getElem_ofFn]
  simp only
  rw [ite_eq_left (by omega)]
  congr 2
  omega

theorem rep_letters :
    ∀ j < (chainLetters orb).size / 2, Rep 22880 (chainLetters orb)[2 * j]! (gs j) := by
  intro j hj
  rw [chainLetters_size] at hj
  have hj' : j < chainWords.size := by omega
  rw [chainLetters_even hj']
  exact Rep.wordT (by norm_num) _ fun l _ => rep_gen l

noncomputable abbrev trees : Array Tree := chainTrees 22880 (chainLetters orb) chainBase

noncomputable abbrev lvl (i : ℕ) : Subgroup J :=
  levelGroup (chainLetters orb) chainBase (pairG gs) i

theorem chain_facts' :
    (∀ i < chainBase.size, TreeFacts 22880 trees[i]!
      (levelLetters (chainLetters orb) chainBase i) (pairG gs) chainBase[i]!) ∧
      (∀ i < chainBase.size, ∀ g ∈ lvl i, idx 22880 g chainBase[i]! = chainBase[i]! ↔
        g ∈ lvl (i + 1)) ∧
      ∀ i ≤ chainBase.size, Nat.card (lvl i) =
        ∏ l ∈ Finset.Ico i chainBase.size, trees[l]!.pts.size :=
  chain_facts rep_letters sep actionChecks_parts.2.2.2.2.2.2.1

theorem chainBase_size : chainBase.size = 4 := rfl

theorem tree_size_of
    {l v : ℕ} (hv : [22880, 8505, 144, 16][l]? = some v) :
    trees[l]!.pts.size = v := by
  have h := actionChecks_parts.2.2.2.2.2.2.2.1
  have h2 := congrArg (fun L : List ℕ => L[l]?) h
  simp only [orbitSizes, List.getElem?_map, Array.getElem?_toList] at h2
  rw [hv] at h2
  have hl : l < trees.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at h2
    simp at h2
  rw [Array.getElem?_eq_getElem hl] at h2
  simp only [Option.map_some, Option.some.injEq] at h2
  rw [getElem!_pos trees l hl]
  exact h2

theorem card_lvl_one : Nat.card (lvl 1) = 19595520 := by
  rw [chain_facts'.2.2 1 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 1 4, trees[l]!.pts.size =
      [22880, 8505, 144, 16].getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem card_lvl_zero : Nat.card (lvl 0) = 448345497600 := by
  rw [chain_facts'.2.2 0 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 0 4, trees[l]!.pts.size =
      [22880, 8505, 144, 16].getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem chainWords_zero : chainWords[0]! = [1] := by decide

theorem chainWords_one : chainWords[1]! = [2] := by decide

theorem chainWords_size : chainWords.size = 14 := by decide

theorem chainBase_zero : chainBase[0]! = 0 := by decide

theorem chainBase_one : chainBase[1]! = 1 := by decide

theorem gs_zero : gs 0 = a := by
  rw [gs, chainWords_zero]; simp [wordG, genG]

theorem gs_one : gs 1 = b := by
  rw [gs, chainWords_one]; simp [wordG, genG]

theorem lvl_zero : lvl 0 = ⊤ := by
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  have hsz : 2 < (chainLetters orb).size := by rw [chainLetters_size, chainWords_size]; decide
  rintro _ (rfl | rfl)
  · have : pairG gs 0 = a := by simp [pairG, gs_zero]
    rw [← this]
    exact lG_mem (mem_levelLetters_zero.2 (by omega))
  · have : pairG gs 2 = b := by simp [pairG, gs_one]
    rw [← this]
    exact lG_mem (mem_levelLetters_zero.2 hsz)

theorem mem_lvl_zero (g : J) : g ∈ lvl 0 := by rw [lvl_zero]; trivial

noncomputable abbrev root : Fin 22880 := ⟨0, by norm_num⟩

theorem lvl_one_iff (g : J) : idx 22880 g 0 = 0 ↔ g ∈ lvl 1 := by
  have := chain_facts'.2.1 0 (by rw [chainBase_size]; norm_num) g (mem_lvl_zero g)
  rwa [chainBase_zero] at this

theorem stabilizer_root : MulAction.stabilizer J root = lvl 1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← lvl_one_iff, idx_of_lt g (by norm_num : 0 < 22880)]
  constructor
  · intro h; rw [h]
  · intro h; exact Fin.ext h

theorem card_stabilizer_root :
    Nat.card (MulAction.stabilizer J root) = 19595520 := by
  rw [stabilizer_root]; exact card_lvl_one

theorem lvl_one_fix {g : J} (hg : g ∈ lvl 1) : g • root = root := by
  rw [← MulAction.mem_stabilizer_iff, stabilizer_root]; exact hg

theorem treeFacts_zero :
    TreeFacts 22880 trees[0]! (levelLetters (chainLetters orb) chainBase 0)
    (pairG gs) 0 := by
  have := chain_facts'.1 0 (by rw [chainBase_size]; norm_num)
  rwa [chainBase_zero] at this

instance isPretransitive :
    MulAction.IsPretransitive J (Fin 22880) := by
  have hT := treeFacts_zero
  have hcard := hT.card_orbit
  rw [tree_size_of (l := 0) rfl] at hcard
  set O := MulAction.orbit (lettersGroup (levelLetters (chainLetters orb) chainBase 0) (pairG gs))
    (⟨0, hT.r_lt⟩ : Fin 22880) with hO
  have huniv : O = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
  have hreach : ∀ p : Fin 22880, ∃ g : J, g • root = p := by
    intro p
    have hp : p ∈ O := by rw [huniv]; trivial
    obtain ⟨⟨g, _⟩, hg⟩ := hp
    exact ⟨g, hg⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, hg⟩ := hreach p
  obtain ⟨h, hh⟩ := hreach q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

noncomputable abbrev lv1 : Array ℕ := levelLetters (chainLetters orb) chainBase 1

noncomputable abbrev Tj (j : ℕ) : Tree := treeBFS 22880 subRoots[j]! (chainLetters orb) lv1

theorem rep_pairG_all :
    ∀ l < (chainLetters orb).size, Rep 22880 (chainLetters orb)[l]! (pairG gs l) :=
  rep_pairG rep_letters (by rw [chainLetters_size]; omega) (chainOK_parts
    actionChecks_parts.2.2.2.2.2.2.1).2.1

theorem treeFacts_one :
    TreeFacts 22880 trees[1]! lv1 (pairG gs) 1 := by
  have := chain_facts'.1 1 (by rw [chainBase_size]; norm_num)
  rwa [chainBase_one] at this

theorem treeFacts_j
    {j : ℕ} (h : CFSG.Perm.Native.treeOK 22880 subRoots[j]! (Tj j)
    (chainLetters orb) lv1 = true) : TreeFacts 22880 (Tj j) lv1 (pairG gs) subRoots[j]! :=
  treeOK_facts (fun l hl => rep_pairG_all l (levelLetters_lt hl)) h

theorem treeFacts_2 :
    TreeFacts 22880 (Tj 0) lv1 (pairG gs) subRoots[0]! :=
  treeFacts_j actionChecks_parts.2.2.2.2.2.2.2.2.1

theorem treeFacts_3 :
    TreeFacts 22880 (Tj 1) lv1 (pairG gs) subRoots[1]! :=
  treeFacts_j actionChecks_parts.2.2.2.2.2.2.2.2.2.2.1

theorem treeFacts_4 :
    TreeFacts 22880 (Tj 2) lv1 (pairG gs) subRoots[2]! :=
  treeFacts_j actionChecks_parts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Tj_size_0 :
    (Tj 0).pts.size = 13608 := actionChecks_parts.2.2.2.2.2.2.2.2.2.1

theorem Tj_size_1 :
    (Tj 1).pts.size = 280 := actionChecks_parts.2.2.2.2.2.2.2.2.2.2.2.1

theorem Tj_size_2 :
    (Tj 2).pts.size = 486 := actionChecks_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem lvl_one_eq : lettersGroup lv1 (pairG gs) = lvl 1 := rfl

@[expose] def InTree (T : Tree) (p : ℕ) : Prop :=
  ap T.pos p < T.pts.size ∧ ap T.pts (ap T.pos p) = p

instance (T : Tree) (p : ℕ) : Decidable (InTree T p) := by unfold InTree; infer_instance

theorem inTree_iff_inT (T : Tree) (p : ℕ) : InTree T p ↔ inT T p = true := by
  unfold InTree inT
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]

theorem inTree_iff
    {T : Tree} {lv : Array ℕ} {r : ℕ} (hT : TreeFacts 22880 T lv (pairG gs) r)
    (p : Fin 22880) :
    InTree T p.val ↔
      p ∈ MulAction.orbit (lettersGroup lv (pairG gs)) (⟨r, hT.r_lt⟩ : Fin 22880) := by
  rw [hT.mem_orbit_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, h2⟩
  · rintro ⟨k, hk, hkp⟩
    refine ⟨?_, ?_⟩
    · rw [← hkp, hT.pos_pts k hk]; exact hk
    · rw [← hkp, hT.pos_pts k hk]

theorem orbit_smul_mem
    {H : Subgroup J} {x p : Fin 22880} (h : J) (hh : h ∈ H)
    (hp : p ∈ MulAction.orbit H x) : h • p ∈ MulAction.orbit H x := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := hp
  refine ⟨⟨h * k, H.mul_mem hh hk⟩, ?_⟩
  show (h * k) • x = h • (k • x)
  exact mul_smul h k x

theorem inTree_smul
    {T : Tree} {r : ℕ} (hT : TreeFacts 22880 T lv1 (pairG gs) r) {h : J}
    (hh : h ∈ lvl 1) (p : Fin 22880) : InTree T (h • p).val ↔ InTree T p.val := by
  rw [inTree_iff hT, inTree_iff hT]
  constructor
  · intro hp
    have := orbit_smul_mem h⁻¹ ((lvl 1).inv_mem hh) hp
    rwa [inv_smul_smul] at this
  · exact orbit_smul_mem h hh

theorem smul_eq_root_iff {h : J} (hh : h ∈ lvl 1) (p : Fin 22880) :
    (h • p).val = 0 ↔ p.val = 0 := by
  constructor
  · intro e
    have e' : h • p = root := Fin.ext e
    have := congrArg (fun q => h⁻¹ • q) e'
    simp only [inv_smul_smul] at this
    rw [this, lvl_one_fix ((lvl 1).inv_mem hh)]
  · intro e
    have e' : p = root := Fin.ext e
    rw [e', lvl_one_fix hh]

@[expose] noncomputable def subLab (p : Fin 22880) : Fin 5 :=
  if p.val = 0 then 0 else if InTree trees[1]! p.val then 1 else if InTree (Tj 0) p.val then 2
  else if InTree (Tj 1) p.val then 3 else 4

theorem subLab_inv :
    ∀ h ∈ lvl 1, ∀ p : Fin 22880, subLab (h • p) = subLab p := by
  intro h hh p
  unfold subLab
  simp only [smul_eq_root_iff hh, inTree_smul treeFacts_one hh, inTree_smul treeFacts_2 hh,
    inTree_smul treeFacts_3 hh]

theorem connect
    {x p q : Fin 22880} {H : Subgroup J} (hp : p ∈ MulAction.orbit H x)
    (hq : q ∈ MulAction.orbit H x) : ∃ h ∈ H, h • p = q := by
  obtain ⟨⟨u, hu⟩, rfl⟩ := hp
  obtain ⟨⟨v, hv⟩, rfl⟩ := hq
  refine ⟨v * u⁻¹, H.mul_mem hv (H.inv_mem hu), ?_⟩
  show (v * u⁻¹) • (u • x) = v • x
  rw [mul_smul, inv_smul_smul]

theorem cover
    (p : Fin 22880) : p.val = 0 ∨ InTree trees[1]! p.val ∨ InTree (Tj 0) p.val ∨
    InTree (Tj 1) p.val ∨ InTree (Tj 2) p.val := by
  rcases actionChecks_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p.val p.isLt with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ((inTree_iff_inT _ _).2 h))
  · exact Or.inr (Or.inr (Or.inl ((inTree_iff_inT _ _).2 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ((inTree_iff_inT _ _).2 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ((inTree_iff_inT _ _).2 h))))

theorem subLab_mem (p : Fin 22880) :
    (subLab p = 0 → p = root) ∧
    (subLab p = 1 → InTree trees[1]! p.val) ∧
    (subLab p = 2 → InTree (Tj 0) p.val) ∧
    (subLab p = 3 → InTree (Tj 1) p.val) ∧
    (subLab p = 4 → InTree (Tj 2) p.val) := by
  unfold subLab
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    split_ifs at h with h0 h1 h2 h3 <;> first | exact absurd h (by decide) | skip
  · exact Fin.ext h0
  · exact h1
  · exact h2
  · exact h3
  · rcases cover p with c | c | c | c | c
    · exact absurd c h0
    · exact absurd c h1
    · exact absurd c h2
    · exact absurd c h3
    · exact c

theorem subLab_orb :
    ∀ p q : Fin 22880, subLab p = subLab q → ∃ h ∈ lvl 1, h • p = q := by
  intro p q hpq
  have hcases : subLab p = 0 ∨ subLab p = 1 ∨ subLab p = 2 ∨ subLab p = 3 ∨ subLab p = 4 := by
    rcases subLab p with ⟨_ | _ | _ | _ | _ | n, hn⟩
    · left; rfl
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; left; rfl
    · right; right; right; right; rfl
    · omega
  rcases hcases with h | h | h | h | h
  · rw [(subLab_mem p).1 h, (subLab_mem q).1 (hpq ▸ h)]
    exact ⟨1, (lvl 1).one_mem, one_smul _ _⟩
  · exact connect ((inTree_iff treeFacts_one p).1 ((subLab_mem p).2.1 h))
      ((inTree_iff treeFacts_one q).1 ((subLab_mem q).2.1 (hpq ▸ h)))
  · exact connect ((inTree_iff treeFacts_2 p).1 ((subLab_mem p).2.2.1 h))
      ((inTree_iff treeFacts_2 q).1 ((subLab_mem q).2.2.1 (hpq ▸ h)))
  · exact connect ((inTree_iff treeFacts_3 p).1 ((subLab_mem p).2.2.2.1 h))
      ((inTree_iff treeFacts_3 q).1 ((subLab_mem q).2.2.2.1 (hpq ▸ h)))
  · exact connect ((inTree_iff treeFacts_4 p).1 ((subLab_mem p).2.2.2.2 h))
      ((inTree_iff treeFacts_4 q).1 ((subLab_mem q).2.2.2.2 (hpq ▸ h)))

theorem card_le_tree
    {T : Tree} {lv : Array ℕ} {r : ℕ} (hT : TreeFacts 22880 T lv (pairG gs) r)
    (i : Fin 5) (h : ∀ p : Fin 22880, subLab p = i → InTree T p.val) :
    (Finset.univ.filter (fun p : Fin 22880 => subLab p = i)).card ≤ T.pts.size := by
  classical
  rw [← hT.card_orbit, Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ (Set.toFinite _)
  intro p hp
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp
  exact (inTree_iff hT p).1 (h p hp)

theorem card_subLab_zero :
    (Finset.univ.filter (fun p : Fin 22880 => subLab p = 0)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨root, ?_⟩
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · exact (subLab_mem p).1
  · rintro rfl; simp [subLab]

@[expose] def subSizes : Fin 5 → ℕ := ![1, 8505, 13608, 280, 486]

theorem card_subLab (i : Fin 5) :
    (Finset.univ.filter (fun p : Fin 22880 => subLab p = i)).card = subSizes i := by
  have h := Finset.card_eq_sum_card_fiberwise (f := subLab) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h0 := card_subLab_zero
  have h1 := card_le_tree treeFacts_one 1 fun p hp => (subLab_mem p).2.1 hp
  have h2 := card_le_tree treeFacts_2 2 fun p hp => (subLab_mem p).2.2.1 hp
  have h3 := card_le_tree treeFacts_3 3 fun p hp => (subLab_mem p).2.2.2.1 hp
  have h4 := card_le_tree treeFacts_4 4 fun p hp => (subLab_mem p).2.2.2.2 hp
  rw [tree_size_of (l := 1) rfl] at h1
  rw [Tj_size_0] at h2
  rw [Tj_size_1] at h3
  rw [Tj_size_2] at h4
  have key : ∀ f : Fin 5 → ℕ, 22880 = ∑ i, f i → f 0 = 1 → f 1 ≤ 8505 → f 2 ≤ 13608 →
      f 3 ≤ 280 → f 4 ≤ 486 → f 1 = 8505 ∧ f 2 = 13608 ∧ f 3 = 280 ∧ f 4 = 486 := by
    intro f h h0 h1 h2 h3 h4
    rw [Fin.sum_univ_five] at h
    omega
  obtain ⟨e1, e2, e3, e4⟩ :=
    key (fun i => (Finset.univ.filter (fun p : Fin 22880 => subLab p = i)).card) h h0 h1 h2 h3 h4
  fin_cases i
  · exact h0
  · exact e1
  · exact e2
  · exact e3
  · exact e4

theorem subSizes_blocks : ∀ S : Finset (Fin 5), (0 : Fin 5) ∈ S →
    (∑ i ∈ S, subSizes i) ∣ 22880 → S = {0} ∨ S = Finset.univ := by
  decide

theorem isPreprimitive : MulAction.IsPreprimitive J (Fin 22880) := by
  apply isPreprimitive_of_suborbit_labels root (lvl 1) (fun h hh => lvl_one_fix hh) subLab
    subLab_inv subLab_orb
  intro S hS hdvd
  have h0 : subLab root = 0 := by simp [subLab]
  rw [h0] at hS ⊢
  have hsum : (∑ i ∈ S, (Finset.univ.filter (fun p : Fin 22880 => subLab p = i)).card) =
      ∑ i ∈ S, subSizes i := Finset.sum_congr rfl fun i _ => card_subLab i
  rw [hsum, Fintype.card_fin] at hdvd
  exact subSizes_blocks S hS hdvd

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

theorem orderOf_a : orderOf a = 2 := orderOf_eq_prime a_sq a_ne_one

theorem orderOf_b : orderOf b = 3 := orderOf_eq_prime b_cube b_ne_one

theorem orderOf_ab :
    orderOf (a * b) = 13 := orderOf_eq_prime ab_pow ab_ne_one

theorem isSimpleGroup_J : IsSimpleGroup J := by
  have := isPreprimitive
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Fin 22880) ?_ a b closure_ab root ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  · rw [orderOf_a, orderOf_b]; norm_num
  · rw [orderOf_ab, card_stabilizer_root]; norm_num

theorem card_J : Nat.card J = 448345497600 := by
  rw [← card_lvl_zero, lvl_zero, Subgroup.card_top]

theorem isSimpleGroup_Suz : IsSimpleGroup NativeSporadic.Suz :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J suzEquivJ

theorem card_Suz : Nat.card NativeSporadic.Suz = 448345497600 := by
  rw [Nat.card_congr suzEquivJ.toEquiv, card_J]

theorem fam_suz_simplicity :
    Finite NativeSporadic.Suz ∧ Nontrivial NativeSporadic.Suz ∧
    IsSimpleGroup NativeSporadic.Suz :=
  ⟨inferInstance, isSimpleGroup_Suz.toNontrivial, isSimpleGroup_Suz⟩

end CFSG.Sporadic.Suz
