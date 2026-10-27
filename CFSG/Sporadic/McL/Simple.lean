module

public import CFSG.Sporadic.McL.Action
public import CFSG.Perm.ChainSpec

public section

namespace CFSG.Sporadic.McL

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Blueprint

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def genG (z : ℤ) : J :=
  if z = 1 then a else if z = -1 then a⁻¹ else if z = 2 then b else b⁻¹

theorem rep_alpha_inv : Rep 275 orb.alpha a⁻¹ :=
  Rep.inv_of_invoOK rep_alpha actionChecks_parts.2.2.2.1

theorem rep_gen (z : ℤ) : Rep 275 (genTables orb z) (genG z) := by
  unfold genTables genG
  by_cases h1 : z = 1
  · subst h1; simp only [true_or, ite_true]; exact rep_alpha
  · by_cases h2 : z = -1
    · subst h2
      simp only [or_true, ite_true, show (-1 : ℤ) ≠ 1 by decide, ite_false]
      exact rep_alpha_inv
    · by_cases h3 : z = 2
      · subst h3
        simp only [show (2 : ℤ) ≠ 1 by decide, show (2 : ℤ) ≠ -1 by decide, or_self, ite_false,
          ite_true]
        exact rep_beta
      · simp only [h1, h2, h3, or_self, ite_false]
        exact Rep.inv_of_invOK rep_beta actionChecks_parts.2.2.2.2.1

@[expose] noncomputable def gs
    (j : ℕ) : J := wordG genG chainWords[j]!

theorem chainLetters_size : (chainLetters orb).size = 2 * chainWords.size := by
  unfold chainLetters buildLetters; simp

theorem chainLetters_even {j : ℕ} (hj : j < chainWords.size) :
    (chainLetters orb)[2 * j]! = wordT 275 (genTables orb) chainWords[j]! := by
  unfold chainLetters buildLetters
  rw [getElem!_pos _ (2 * j) (by simp; omega), Array.getElem_ofFn]
  simp only
  rw [ite_eq_left (by omega)]
  congr 2
  omega

theorem rep_letters :
    ∀ j < (chainLetters orb).size / 2, Rep 275 (chainLetters orb)[2 * j]! (gs j) := by
  intro j hj
  rw [chainLetters_size] at hj
  have hj' : j < chainWords.size := by omega
  rw [chainLetters_even hj']
  exact Rep.wordT (by norm_num) _ fun l _ => rep_gen l

noncomputable abbrev trees : Array Tree := chainTrees 275 (chainLetters orb) chainBase

noncomputable abbrev lvl (i : ℕ) : Subgroup J :=
  levelGroup (chainLetters orb) chainBase (pairG gs) i

theorem chain_facts' :
    (∀ i < chainBase.size, TreeFacts 275 trees[i]! (levelLetters (chainLetters orb) chainBase i)
      (pairG gs) chainBase[i]!) ∧
      (∀ i < chainBase.size, ∀ g ∈ lvl i, idx 275 g chainBase[i]! = chainBase[i]! ↔
        g ∈ lvl (i + 1)) ∧
      ∀ i ≤ chainBase.size, Nat.card (lvl i) =
        ∏ l ∈ Finset.Ico i chainBase.size, trees[l]!.pts.size :=
  chain_facts rep_letters sep actionChecks_parts.2.2.2.2.2.2.2.2.1

theorem chainBase_size : chainBase.size = 6 := rfl

theorem tree_size_of
    {l v : ℕ} (hv : [275, 162, 56, 30, 4, 3][l]? = some v) :
    trees[l]!.pts.size = v := by
  have h := actionChecks_parts.2.2.2.2.2.2.2.2.2.1
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

theorem card_lvl_one : Nat.card (lvl 1) = 3265920 := by
  rw [chain_facts'.2.2 1 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 1 6, trees[l]!.pts.size =
      [275, 162, 56, 30, 4, 3].getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem card_lvl_zero : Nat.card (lvl 0) = 898128000 := by
  rw [chain_facts'.2.2 0 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 0 6, trees[l]!.pts.size =
      [275, 162, 56, 30, 4, 3].getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem chainWords_zero : chainWords[0]! = [1] := by decide

theorem chainWords_one : chainWords[1]! = [2] := by decide

theorem chainWords_size : chainWords.size = 9 := by decide

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

noncomputable abbrev root : Fin 275 := ⟨0, by norm_num⟩

theorem lvl_one_iff (g : J) : idx 275 g 0 = 0 ↔ g ∈ lvl 1 := by
  have := chain_facts'.2.1 0 (by rw [chainBase_size]; norm_num) g (mem_lvl_zero g)
  rwa [chainBase_zero] at this

theorem stabilizer_root : MulAction.stabilizer J root = lvl 1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← lvl_one_iff, idx_of_lt g (by norm_num : 0 < 275)]
  constructor
  · intro h; rw [h]
  · intro h; exact Fin.ext h

theorem card_stabilizer_root :
    Nat.card (MulAction.stabilizer J root) = 3265920 := by
  rw [stabilizer_root]; exact card_lvl_one

theorem lvl_one_fix {g : J} (hg : g ∈ lvl 1) : g • root = root := by
  rw [← MulAction.mem_stabilizer_iff, stabilizer_root]; exact hg

theorem treeFacts_zero :
    TreeFacts 275 trees[0]! (levelLetters (chainLetters orb) chainBase 0)
    (pairG gs) 0 := by
  have := chain_facts'.1 0 (by rw [chainBase_size]; norm_num)
  rwa [chainBase_zero] at this

instance isPretransitive :
    MulAction.IsPretransitive J (Fin 275) := by
  have hT := treeFacts_zero
  have hcard := hT.card_orbit
  rw [tree_size_of (l := 0) rfl] at hcard
  set O := MulAction.orbit (lettersGroup (levelLetters (chainLetters orb) chainBase 0) (pairG gs))
    (⟨0, hT.r_lt⟩ : Fin 275) with hO
  have huniv : O = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
  have hreach : ∀ p : Fin 275, ∃ g : J, g • root = p := by
    intro p
    have hp : p ∈ O := by rw [huniv]; trivial
    obtain ⟨⟨g, _⟩, hg⟩ := hp
    exact ⟨g, hg⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, hg⟩ := hreach p
  obtain ⟨h, hh⟩ := hreach q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

noncomputable abbrev lv1 : Array ℕ := levelLetters (chainLetters orb) chainBase 1

noncomputable abbrev T2 : Tree := treeBFS 275 subRoot (chainLetters orb) lv1

theorem rep_pairG_all :
    ∀ l < (chainLetters orb).size, Rep 275 (chainLetters orb)[l]! (pairG gs l) :=
  rep_pairG rep_letters (by rw [chainLetters_size]; omega) (chainOK_parts
    actionChecks_parts.2.2.2.2.2.2.2.2.1).2.1

theorem treeFacts_one :
    TreeFacts 275 trees[1]! lv1 (pairG gs) 1 := by
  have := chain_facts'.1 1 (by rw [chainBase_size]; norm_num)
  rwa [chainBase_one] at this

theorem treeFacts_two : TreeFacts 275 T2 lv1 (pairG gs) subRoot :=
  treeOK_facts (fun l hl => rep_pairG_all l (levelLetters_lt hl))
    actionChecks_parts.2.2.2.2.2.2.2.2.2.2.1

theorem T2_size :
    T2.pts.size = 112 := actionChecks_parts.2.2.2.2.2.2.2.2.2.2.2.1

@[expose] def InTree (T : Tree) (p : ℕ) : Prop :=
  ap T.pos p < T.pts.size ∧ ap T.pts (ap T.pos p) = p

instance (T : Tree) (p : ℕ) : Decidable (InTree T p) := by unfold InTree; infer_instance

theorem inTree_iff
    {T : Tree} {lv : Array ℕ} {r : ℕ} (hT : TreeFacts 275 T lv (pairG gs) r)
    (p : Fin 275) :
    InTree T p.val ↔
      p ∈ MulAction.orbit (lettersGroup lv (pairG gs)) (⟨r, hT.r_lt⟩ : Fin 275) := by
  rw [hT.mem_orbit_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, h2⟩
  · rintro ⟨k, hk, hkp⟩
    refine ⟨?_, ?_⟩
    · rw [← hkp, hT.pos_pts k hk]; exact hk
    · rw [← hkp, hT.pos_pts k hk]

@[expose] noncomputable def subLab (p : Fin 275) : Fin 3 :=
  if p.val = 0 then 0 else if InTree trees[1]! p.val then 1 else 2

theorem orbit_smul_mem
    {H : Subgroup J} {x p : Fin 275} (h : J) (hh : h ∈ H)
    (hp : p ∈ MulAction.orbit H x) : h • p ∈ MulAction.orbit H x := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := hp
  refine ⟨⟨h * k, H.mul_mem hh hk⟩, ?_⟩
  show (h * k) • x = h • (k • x)
  exact mul_smul h k x

theorem inTree_one (p : Fin 275) :
    InTree trees[1]! p.val ↔ p ∈ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 275) :=
  inTree_iff treeFacts_one p

theorem inTree_two (p : Fin 275) :
    InTree T2 p.val ↔
      p ∈ MulAction.orbit (lvl 1) (⟨subRoot, treeFacts_two.r_lt⟩ : Fin 275) :=
  inTree_iff treeFacts_two p

theorem orbit_one_ne_zero (p : Fin 275)
    (hp : p ∈ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 275)) : p.val ≠ 0 := by
  intro h0
  obtain ⟨⟨k, hk⟩, hkp⟩ := hp
  have hp0 : p = root := Fin.ext h0
  have : (k⁻¹ : J) • p = (⟨1, treeFacts_one.r_lt⟩ : Fin 275) := by
    rw [← hkp]
    exact inv_smul_smul k _
  rw [hp0, lvl_one_fix ((lvl 1).inv_mem hk)] at this
  exact absurd (Fin.mk.inj this) (by decide)

theorem subLab_eq_zero {p : Fin 275} : subLab p = 0 ↔ p = root := by
  unfold subLab
  constructor
  · intro h
    by_contra hp
    have hp' : p.val ≠ 0 := fun e => hp (Fin.ext e)
    rw [ite_eq_right hp'] at h
    split_ifs at h <;> exact absurd h (by decide)
  · rintro rfl; simp

theorem subLab_eq_one {p : Fin 275} :
    subLab p = 1 ↔ p ∈ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 275) := by
  rw [← inTree_one p]
  unfold subLab
  constructor
  · intro h
    split_ifs at h with h0 h1
    · exact absurd h (by decide)
    · exact h1
    · exact absurd h (by decide)
  · intro h
    have h0 : p.val ≠ 0 := orbit_one_ne_zero p ((inTree_one p).1 h)
    rw [ite_eq_right h0, ite_eq_left h]

theorem subLab_eq_two {p : Fin 275} :
    subLab p = 2 ↔ p ≠ root ∧ p ∉ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 275) := by
  rw [← inTree_one p]
  unfold subLab
  constructor
  · intro h
    split_ifs at h with h0 h1
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact ⟨fun e => h0 (congrArg Fin.val e), h1⟩
  · rintro ⟨h0, h1⟩
    have h0' : p.val ≠ 0 := fun e => h0 (Fin.ext e)
    rw [ite_eq_right h0', ite_eq_right h1]

theorem two_mem_orbit {p : Fin 275} (h : subLab p = 2) :
    p ∈ MulAction.orbit (lvl 1) (⟨subRoot, treeFacts_two.r_lt⟩ : Fin 275) := by
  obtain ⟨h0, h1⟩ := subLab_eq_two.1 h
  rw [← inTree_one p] at h1
  rcases actionChecks_parts.2.2.2.2.2.2.2.2.2.2.2.2 p.val p.isLt with hc | hc | hc
  · exact absurd (Fin.ext hc) h0
  · exact absurd hc h1
  · exact (inTree_two p).1 ⟨by rw [T2_size]; exact hc.1, hc.2⟩

theorem subLab_inv :
    ∀ h ∈ lvl 1, ∀ p : Fin 275, subLab (h • p) = subLab p := by
  intro h hh p
  have hinv : h⁻¹ ∈ lvl 1 := (lvl 1).inv_mem hh
  by_cases hp0 : p = root
  · rw [hp0, lvl_one_fix hh]
  by_cases hp1 : p ∈ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 275)
  · rw [subLab_eq_one.2 hp1, subLab_eq_one.2 (orbit_smul_mem h hh hp1)]
  · have h2 : subLab p = 2 := subLab_eq_two.2 ⟨hp0, hp1⟩
    rw [h2, subLab_eq_two]
    refine ⟨fun e => hp0 ?_, fun e => hp1 ?_⟩
    · have := congrArg (fun q => h⁻¹ • q) e
      simp only [inv_smul_smul] at this
      rw [this, lvl_one_fix hinv]
    · have := orbit_smul_mem h⁻¹ hinv e
      rwa [inv_smul_smul] at this

theorem subLab_orb :
    ∀ p q : Fin 275, subLab p = subLab q → ∃ h ∈ lvl 1, h • p = q := by
  intro p q hpq
  have key : ∀ {x : Fin 275} {H : Subgroup J}, p ∈ MulAction.orbit H x →
      q ∈ MulAction.orbit H x → ∃ h ∈ H, h • p = q := by
    intro x H hp hq
    obtain ⟨⟨u, hu⟩, rfl⟩ := hp
    obtain ⟨⟨v, hv⟩, rfl⟩ := hq
    refine ⟨v * u⁻¹, H.mul_mem hv (H.inv_mem hu), ?_⟩
    show (v * u⁻¹) • (u • x) = v • x
    rw [mul_smul, inv_smul_smul]
  have hcases : subLab p = 0 ∨ subLab p = 1 ∨ subLab p = 2 := by
    rcases subLab p with ⟨_ | _ | _ | n, hn⟩
    · left; rfl
    · right; left; rfl
    · right; right; rfl
    · omega
  rcases hcases with h | h | h
  · have hq := hpq ▸ h
    rw [subLab_eq_zero.1 h, subLab_eq_zero.1 hq]
    exact ⟨1, (lvl 1).one_mem, one_smul _ _⟩
  · exact key (subLab_eq_one.1 h) (subLab_eq_one.1 (hpq ▸ h))
  · exact key (two_mem_orbit h) (two_mem_orbit (hpq ▸ h))

theorem card_subLab_one :
    (Finset.univ.filter (fun p : Fin 275 => subLab p = 1)).card = 162 := by
  classical
  have hc := treeFacts_one.card_orbit
  rw [tree_size_of (l := 1) rfl] at hc
  have hset : MulAction.orbit (lettersGroup lv1 (pairG gs)) (⟨1, treeFacts_one.r_lt⟩ : Fin 275) =
      ↑(Finset.univ.filter (fun p : Fin 275 => subLab p = 1)) := by
    ext p
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    exact subLab_eq_one.symm
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
  exact hc

theorem card_subLab_zero :
    (Finset.univ.filter (fun p : Fin 275 => subLab p = 0)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨root, ?_⟩
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact subLab_eq_zero

theorem card_subLab_two :
    (Finset.univ.filter (fun p : Fin 275 => subLab p = 2)).card = 112 := by
  have h := Finset.card_eq_sum_card_fiberwise (f := subLab) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h0 : (Finset.univ.filter (fun p : Fin 275 => subLab p = 0)).card = 1 := card_subLab_zero
  have h1 : (Finset.univ.filter (fun p : Fin 275 => subLab p = 1)).card = 162 := card_subLab_one
  have key : ∀ f : Fin 3 → ℕ, 275 = ∑ i, f i → f 0 = 1 → f 1 = 162 → f 2 = 112 := by
    intro f h h0 h1
    rw [Fin.sum_univ_three] at h
    omega
  exact key (fun i => (Finset.univ.filter (fun p : Fin 275 => subLab p = i)).card) h h0 h1

@[expose] def subSizes : Fin 3 → ℕ := ![1, 162, 112]

theorem subSizes_blocks : ∀ S : Finset (Fin 3), (0 : Fin 3) ∈ S →
    (∑ i ∈ S, subSizes i) ∣ 275 → S = {0} ∨ S = Finset.univ := by
  decide

theorem card_subLab (i : Fin 3) :
    (Finset.univ.filter (fun p : Fin 275 => subLab p = i)).card = subSizes i := by
  fin_cases i
  · exact card_subLab_zero
  · exact card_subLab_one
  · exact card_subLab_two

theorem isPreprimitive : MulAction.IsPreprimitive J (Fin 275) := by
  apply isPreprimitive_of_suborbit_labels root (lvl 1) (fun h hh => lvl_one_fix hh) subLab
    subLab_inv subLab_orb
  intro S hS hdvd
  have h0 : subLab root = 0 := subLab_eq_zero.2 rfl
  rw [h0] at hS ⊢
  have hsum : (∑ i ∈ S, (Finset.univ.filter (fun p : Fin 275 => subLab p = i)).card) =
      ∑ i ∈ S, subSizes i := Finset.sum_congr rfl fun i _ => card_subLab i
  rw [hsum, Fintype.card_fin] at hdvd
  exact subSizes_blocks S hS hdvd

theorem a_sq : a ^ 2 = 1 := by
  apply mat_injective
  rw [mat_pow, mat_one, mat_a, toMat_matA, pow_two]
  exact matrixFacts.A_sq

theorem a_ne_one : a ≠ 1 := by
  intro h
  apply matrixFacts.A_ne
  have := congrArg mat h
  rwa [mat_a, toMat_matA, mat_one] at this

theorem b_pow : b ^ 5 = 1 := by
  apply mat_injective
  rw [mat_pow, mat_one, mat_b, toMat_matB]
  exact matrixFacts.B_pow

theorem b_ne_one : b ≠ 1 := by
  intro h
  apply matrixFacts.B_ne
  have := congrArg mat h
  rwa [mat_b, toMat_matB, mat_one] at this

theorem ab_pow : (a * b) ^ 11 = 1 := by
  apply mat_injective
  rw [mat_pow, mat_one, mat_mul, mat_a, mat_b, toMat_matA, toMat_matB]
  exact matrixFacts.AB_pow

theorem ab_ne_one : a * b ≠ 1 := by
  intro h
  apply matrixFacts.AB_ne
  have := congrArg mat h
  rwa [mat_mul, mat_a, mat_b, toMat_matA, toMat_matB, mat_one] at this

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem orderOf_a : orderOf a = 2 := orderOf_eq_prime a_sq a_ne_one

theorem orderOf_b : orderOf b = 5 := orderOf_eq_prime b_pow b_ne_one

theorem orderOf_ab :
    orderOf (a * b) = 11 := orderOf_eq_prime ab_pow ab_ne_one

theorem isSimpleGroup_J : IsSimpleGroup J := by
  have := isPreprimitive
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Fin 275) ?_ a b closure_ab root ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  · rw [orderOf_a, orderOf_b]; norm_num
  · rw [orderOf_ab, card_stabilizer_root]; norm_num

theorem card_J : Nat.card J = 898128000 := by
  rw [← card_lvl_zero, lvl_zero, Subgroup.card_top]

theorem isSimpleGroup_McL : IsSimpleGroup NativeSporadic.McL :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J mclEquivJ

theorem card_McL : Nat.card NativeSporadic.McL = 898128000 := by
  rw [Nat.card_congr mclEquivJ.toEquiv, card_J]

theorem fam_mcl_simplicity :
    Finite NativeSporadic.McL ∧ Nontrivial NativeSporadic.McL ∧
    IsSimpleGroup NativeSporadic.McL :=
  ⟨inferInstance, isSimpleGroup_McL.toNontrivial, isSimpleGroup_McL⟩

end CFSG.Sporadic.McL
