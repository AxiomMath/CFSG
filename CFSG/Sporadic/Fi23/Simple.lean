
module

public import CFSG.Sporadic.Fi23.SimpleBase
import all CFSG.Sporadic.Fi23.SimpleBase

public import CFSG.Sporadic.Fi23.Class
public import CFSG.Sporadic.Fi23.SlpSpec
public import CFSG.Perm.ChainSpec
public import CFSG.F3.SepSpec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Fi23

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

theorem commute_of_idx_fix
    {g : J} {r : ℕ} (hr : r < 31671) (h : idx 31671 g r = r) :
    mat g * toMatW 253 orb.keys[r]! = toMatW 253 orb.keys[r]! * mat g := by
  have e := (idx_eq_iff hr hr).1 h
  have e2 : g * conjPt r = conjPt r * g := by
    calc g * conjPt r = g * conjPt r * g⁻¹ * g := by rw [inv_mul_cancel_right]
      _ = conjPt r * g := by rw [e]
  have hr' : r < orb.keys.size := by rw [orb_size]; exact hr
  rw [← conjPt_mat r hr', ← mat_mul, ← mat_mul, e2]

theorem chainQ_lt
    {t : ℕ} (ht : t < chainQ.size) : chainQ[t]! < 31671 := by
  have h := actionFacts.q_lt
  rw [Array.all_eq_true] at h
  rw [getElem!_pos chainQ t ht]
  simpa using h t ht

theorem sep
    (g : J) (hg : ∀ t < chainQ.size, idx 31671 g chainQ[t]! = chainQ[t]!) : g = 1 := by
  obtain ⟨c, hc⟩ := scalar_of_sepOK actionFacts.sep (mat g) (fun i hi => by
    have hi' : i < chainQ.size := by simpa using hi
    have e : (chainQ.map fun r => toVM orb.keys[r]!)[i]! = toVM orb.keys[chainQ[i]!]! := by
      rw [getElem!_pos _ i hi, Array.getElem_map, getElem!_pos chainQ i hi']
    rw [e]
    exact commute_of_idx_fix (chainQ_lt hi') (hg i hi'))
  have hdet := det_eq_one g
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc1 := zmod3_pow253 c hdet
  apply mat_injective
  rw [hc, hc1, one_smul]
  rfl

theorem eq_one_of_fix_all
    {g : J} (h : ∀ i : Fin 31671, g • i = i) : g = 1 := by
  apply sep
  intro t ht
  rw [idx_of_lt g (chainQ_lt ht), h]

instance faithful : FaithfulSMul J (Fin 31671) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := eq_one_of_fix_all fun i => by rw [mul_smul, hgh, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem eq_one_of_isIdT
    {T : Table} {g : J} (hT : Rep 31671 T g) (h : isIdT T = true) : g = 1 := by
  apply eq_one_of_fix_all
  intro i
  apply Fin.ext
  have := (allIn_eq_true.1 h) i.val (Nat.zero_le _) i.isLt
  rw [beq_iff_eq, hT i.val i.isLt, idx_of_lt g i.isLt] at this
  exact this

theorem ne_one_of_isIdT
    {T : Table} {g : J} (hT : Rep 31671 T g) (h : isIdT T = false) :
    g ≠ 1 := by
  rintro rfl
  unfold isIdT at h
  rw [← Bool.not_eq_true, allIn_eq_true] at h
  apply h
  intro i _ hi
  rw [beq_iff_eq, hT i hi, idx_one]

@[expose] noncomputable def genG (z : ℤ) : J :=
  if z = 1 then a else if z = -1 then a⁻¹ else if z = 2 then b else b⁻¹

theorem rep_gen (z : ℤ) : Rep 31671 (genTables orb z) (genG z) := by
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
        exact Rep.inv_of_invOK rep_beta actionFacts.beta_inv

@[expose] noncomputable def gs (j : ℕ) : J := slpG genG chainWords j

theorem letters_size : letters.size = 2 * chainWords.size :=
  (slpInv_full (n := 31671) (gens := genTables orb) actionFacts.slp_ok).1

theorem rep_letters :
    ∀ j < letters.size / 2, Rep 31671 letters[2 * j]! (gs j) := by
  intro j hj
  rw [letters_size] at hj
  have hinv := (chainOK_parts actionFacts.chain).2.1
  refine rep_slpLetters (by norm_num) rep_gen actionFacts.slp_ok (fun i hi => ?_) j
    (by omega)
  exact hinv i (by rw [letters_size]; omega)

noncomputable abbrev lvl
    (i : ℕ) : Subgroup J := levelGroup letters chainBase (pairG gs) i

theorem chain_facts' :
    (∀ i < chainBase.size, TreeFacts 31671 trees[i]! (levelLetters letters chainBase i)
      (pairG gs) chainBase[i]!) ∧
      (∀ i < chainBase.size, ∀ g ∈ lvl i, idx 31671 g chainBase[i]! = chainBase[i]! ↔
        g ∈ lvl (i + 1)) ∧
      ∀ i ≤ chainBase.size, Nat.card (lvl i) =
        ∏ l ∈ Finset.Ico i chainBase.size, trees[l]!.pts.size :=
  chain_facts rep_letters sep actionFacts.chain

theorem tree_size_of
    {l v : ℕ} (hv : [31671, 3510, 25344, 288, 1260, 4][l]? = some v) :
    trees[l]!.pts.size = v := by
  have h := actionFacts.sizes
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

theorem card_lvl_one : Nat.card (lvl 1) = 129123503308800 := by
  rw [chain_facts'.2.2 1 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 1 6, trees[l]!.pts.size =
      [31671, 3510, 25344, 288, 1260, 4].getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem card_lvl_zero : Nat.card (lvl 0) = 4089470473293004800 := by
  rw [chain_facts'.2.2 0 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 0 6, trees[l]!.pts.size =
      [31671, 3510, 25344, 288, 1260, 4].getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem rep_pairG_all :
    ∀ l < letters.size, Rep 31671 letters[l]! (pairG gs l) :=
  rep_pairG rep_letters (by rw [letters_size]; omega) (chainOK_parts actionFacts.chain).2.1

theorem walkFacts {i : ℕ} (hi : i < chainBase.size) :
    WalkFacts 31671 trees[i]! letters (pairG gs) := by
  intro k hk hk0
  obtain ⟨hpar, hlab⟩ := (chain_facts'.1 i hi).par k hk hk0
  have hl := levelLetters_lt hlab
  refine ⟨hpar, rep_pairG_all _ hl, ?_⟩
  rw [← pairG_invL]
  exact rep_pairG_all _ (invL_lt (by rw [letters_size]; omega) hl)

theorem mem_lvl_zero_of_sift
    {g : J} {img : Array ℕ} (hsz : img.size = chainQ.size)
    (himg : ∀ t < chainQ.size, img[t]! = idx 31671 g chainQ[t]!)
    (h : sift trees letters chainQb chainQ 0 img = true) : g ∈ lvl 0 := by
  have htrees : trees.size = chainBase.size := (chainOK_parts actionFacts.chain).2.2.1
  refine sift_mem (letters := letters) (lG := pairG gs) (qb := chainQb) sep
    (fun t ht => chainQ_lt ht) (lvl 0) trees.size 0 (by omega) ?_ g img hsz himg h
  intro l' hl' _
  have hl'' : l' < chainBase.size := by rw [← htrees]; exact hl'
  exact ⟨walkFacts hl'', fun k hk => levelGroup_anti (pairG gs) (Nat.zero_le l')
    ((chain_facts'.1 l' hl'').treeG_mem hk)⟩

theorem b_mem_lvl_zero : b ∈ lvl 0 := by
  refine mem_lvl_zero_of_sift (img := apT orb.beta chainQ) (apT_size _ _) (fun t ht => ?_)
    actionFacts.sift_b
  rw [apT_get _ _ ht, rep_beta _ (chainQ_lt ht)]

theorem gs_zero : gs 0 = a := by
  rw [gs, slpG_eq, actionFacts.word0]
  simp [wordG, genG]

theorem a_mem_lvl_zero : a ∈ lvl 0 := by
  have hsz : 0 < letters.size := by rw [letters_size, chainWords_size]; decide
  have : pairG gs 0 = a := by simp [pairG, gs_zero]
  rw [← this]
  exact lG_mem (mem_levelLetters_zero.2 hsz)

theorem lvl_zero : lvl 0 = ⊤ := by
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact a_mem_lvl_zero
  · exact b_mem_lvl_zero

theorem mem_lvl_zero (g : J) : g ∈ lvl 0 := by rw [lvl_zero]; trivial

@[expose] noncomputable def y : J := gs 1

theorem closure_a_y : Subgroup.closure ({a, y} : Set J) = ⊤ := by
  rw [eq_top_iff, ← lvl_zero]
  unfold lvl levelGroup lettersGroup
  rw [Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' := levelLetters_lt hl
  rw [letters_size] at hl'
  have hmem := slpG_mem_closure (gensG := genG) actionFacts.slp_ok actionFacts.slp_pure (l / 2)
    (by omega)
  have e : ({slpG genG chainWords 0, slpG genG chainWords 1} : Set J) = {a, y} := by
    rw [← gs, gs_zero]; rfl
  rw [e] at hmem
  unfold pairG
  split_ifs
  · exact hmem
  · exact Subgroup.inv_mem _ hmem

theorem lvl_one_iff (g : J) : idx 31671 g 0 = 0 ↔ g ∈ lvl 1 := by
  have := chain_facts'.2.1 0 (by rw [chainBase_size]; norm_num) g (mem_lvl_zero g)
  rwa [chainBase_zero] at this

theorem stabilizer_root : MulAction.stabilizer J root = lvl 1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← lvl_one_iff, idx_of_lt g (by norm_num : 0 < 31671)]
  constructor
  · intro h; rw [h]
  · intro h; exact Fin.ext h

theorem card_stabilizer_root :
    Nat.card (MulAction.stabilizer J root) = 129123503308800 := by
  rw [stabilizer_root]; exact card_lvl_one

theorem lvl_one_fix {g : J} (hg : g ∈ lvl 1) : g • root = root := by
  rw [← MulAction.mem_stabilizer_iff, stabilizer_root]; exact hg

theorem treeFacts_zero :
    TreeFacts 31671 trees[0]! (levelLetters letters chainBase 0)
    (pairG gs) 0 := by
  have := chain_facts'.1 0 (by rw [chainBase_size]; norm_num)
  rwa [chainBase_zero] at this

instance isPretransitive :
    MulAction.IsPretransitive J (Fin 31671) := by
  have hT := treeFacts_zero
  have hcard := hT.card_orbit
  rw [tree_size_of (l := 0) rfl] at hcard
  set O := MulAction.orbit (lettersGroup (levelLetters letters chainBase 0) (pairG gs))
    (⟨0, hT.r_lt⟩ : Fin 31671) with hO
  have huniv : O = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
  have hreach : ∀ p : Fin 31671, ∃ g : J, g • root = p := by
    intro p
    have hp : p ∈ O := by rw [huniv]; trivial
    obtain ⟨⟨g, _⟩, hg⟩ := hp
    exact ⟨g, hg⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, hg⟩ := hreach p
  obtain ⟨h, hh⟩ := hreach q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

theorem treeFacts_one :
    TreeFacts 31671 trees[1]! lv1 (pairG gs) 1 := by
  have := chain_facts'.1 1 (by rw [chainBase_size]; norm_num)
  rwa [chainBase_one] at this

theorem treeFacts_two : TreeFacts 31671 T2 lv1 (pairG gs) subRoot :=
  treeOK_facts (fun l hl => rep_pairG_all l (levelLetters_lt hl)) actionFacts.tree2

theorem lvl_one_eq : lettersGroup lv1 (pairG gs) = lvl 1 := rfl

theorem cover
    (p : ℕ) (hp : p < 31671) : p = 0 ∨ InTree trees[1]! p ∨ InTree T2 p := by
  have := (allIn_eq_true.1 actionFacts.cover) p (Nat.zero_le _) hp
  simp only [Bool.or_eq_true, beq_iff_eq, inTreeB_iff] at this
  rcases this with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem inTree_iff
    {T : Tree} {lv : Array ℕ} {r : ℕ} (hT : TreeFacts 31671 T lv (pairG gs) r)
    (p : Fin 31671) :
    InTree T p.val ↔
      p ∈ MulAction.orbit (lettersGroup lv (pairG gs)) (⟨r, hT.r_lt⟩ : Fin 31671) := by
  rw [hT.mem_orbit_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, h2⟩
  · rintro ⟨k, hk, hkp⟩
    refine ⟨?_, ?_⟩
    · rw [← hkp, hT.pos_pts k hk]; exact hk
    · rw [← hkp, hT.pos_pts k hk]

theorem orbit_smul_mem
    {H : Subgroup J} {x p : Fin 31671} (h : J) (hh : h ∈ H)
    (hp : p ∈ MulAction.orbit H x) : h • p ∈ MulAction.orbit H x := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := hp
  refine ⟨⟨h * k, H.mul_mem hh hk⟩, ?_⟩
  show (h * k) • x = h • (k • x)
  exact mul_smul h k x

theorem inTree_one (p : Fin 31671) :
    InTree trees[1]! p.val ↔ p ∈ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 31671) :=
  inTree_iff treeFacts_one p

theorem inTree_two (p : Fin 31671) :
    InTree T2 p.val ↔
      p ∈ MulAction.orbit (lvl 1) (⟨subRoot, treeFacts_two.r_lt⟩ : Fin 31671) :=
  inTree_iff treeFacts_two p

theorem orbit_one_ne_zero (p : Fin 31671)
    (hp : p ∈ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 31671)) : p.val ≠ 0 := by
  intro h0
  obtain ⟨⟨k, hk⟩, hkp⟩ := hp
  have hp0 : p = root := Fin.ext h0
  have : (k⁻¹ : J) • p = (⟨1, treeFacts_one.r_lt⟩ : Fin 31671) := by
    rw [← hkp]
    exact inv_smul_smul k _
  rw [hp0, lvl_one_fix ((lvl 1).inv_mem hk)] at this
  exact Nat.zero_ne_one (congrArg Fin.val this)

theorem subLab_eq_one {p : Fin 31671} :
    subLab p = 1 ↔ p ∈ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 31671) := by
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

theorem subLab_eq_two {p : Fin 31671} :
    subLab p = 2 ↔
      p ≠ root ∧ p ∉ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 31671) := by
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

theorem two_mem_orbit {p : Fin 31671} (h : subLab p = 2) :
    p ∈ MulAction.orbit (lvl 1) (⟨subRoot, treeFacts_two.r_lt⟩ : Fin 31671) := by
  obtain ⟨h0, h1⟩ := subLab_eq_two.1 h
  rw [← inTree_one p] at h1
  rcases cover p.val p.isLt with hc | hc | hc
  · exact absurd (Fin.ext hc) h0
  · exact absurd hc h1
  · exact (inTree_two p).1 hc

theorem subLab_inv :
    ∀ h ∈ lvl 1, ∀ p : Fin 31671, subLab (h • p) = subLab p := by
  intro h hh p
  have hinv : h⁻¹ ∈ lvl 1 := (lvl 1).inv_mem hh
  by_cases hp0 : p = root
  · rw [hp0, lvl_one_fix hh]
  by_cases hp1 : p ∈ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 31671)
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
    ∀ p q : Fin 31671, subLab p = subLab q → ∃ h ∈ lvl 1, h • p = q := by
  intro p q hpq
  have key : ∀ {x : Fin 31671} {H : Subgroup J}, p ∈ MulAction.orbit H x →
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
    (Finset.univ.filter (fun p : Fin 31671 => subLab p = 1)).card = 3510 := by
  classical
  have hc := treeFacts_one.card_orbit
  rw [tree_size_of (l := 1) rfl] at hc
  have hset : MulAction.orbit (lettersGroup lv1 (pairG gs)) (⟨1, treeFacts_one.r_lt⟩ : Fin 31671) =
      ↑(Finset.univ.filter (fun p : Fin 31671 => subLab p = 1)) := by
    ext p
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    exact subLab_eq_one.symm
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
  exact hc

theorem card_subLab_two :
    (Finset.univ.filter (fun p : Fin 31671 => subLab p = 2)).card = 28160 := by
  have h := Finset.card_eq_sum_card_fiberwise (f := subLab) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h0 : (Finset.univ.filter (fun p : Fin 31671 => subLab p = 0)).card = 1 := card_subLab_zero
  have h1 : (Finset.univ.filter (fun p : Fin 31671 => subLab p = 1)).card = 3510 :=
    card_subLab_one
  have key : ∀ f : Fin 3 → ℕ, 31671 = ∑ i, f i → f 0 = 1 → f 1 = 3510 → f 2 = 28160 := by
    intro f h h0 h1
    rw [Fin.sum_univ_three] at h
    omega
  exact key (fun i => (Finset.univ.filter (fun p : Fin 31671 => subLab p = i)).card) h h0 h1

theorem card_subLab (i : Fin 3) :
    (Finset.univ.filter (fun p : Fin 31671 => subLab p = i)).card = subSizes i := by
  fin_cases i
  · exact card_subLab_zero
  · exact card_subLab_one
  · exact card_subLab_two

theorem isPreprimitive : MulAction.IsPreprimitive J (Fin 31671) := by
  apply isPreprimitive_of_suborbit_labels root (lvl 1) (fun h hh => lvl_one_fix hh) subLab
    subLab_inv subLab_orb
  intro S hS hdvd
  have h0 : subLab root = 0 := subLab_eq_zero.2 rfl
  rw [h0] at hS ⊢
  have hsum : (∑ i ∈ S, (Finset.univ.filter (fun p : Fin 31671 => subLab p = i)).card) =
      ∑ i ∈ S, subSizes i := Finset.sum_congr rfl fun i _ => card_subLab i
  rw [hsum, Fintype.card_fin] at hdvd
  exact subSizes_blocks S hS hdvd

theorem a_sq : a ^ 2 = 1 := by
  apply mat_injective
  rw [mat_pow, mat_one, mat_a, pow_two]
  exact matrixFacts.A_sq

theorem a_ne_one : a ≠ 1 := by
  intro h
  apply matrixFacts.A_ne
  rw [← mat_a, h, mat_one]

theorem rep_y :
    Rep 31671 tabY y := rep_letters 1 (by rw [letters_size, chainWords_size]; decide)

theorem rep_ay : Rep 31671 tabAY (a * y) := Rep.compT rep_alpha rep_y

theorem y_pow :
    y ^ 17 = 1 := eq_one_of_isIdT (Rep.powT (by norm_num) rep_y 17) actionFacts.y_pow

theorem y_ne_one : y ≠ 1 := ne_one_of_isIdT rep_y actionFacts.y_ne

theorem ay_pow : (a * y) ^ 23 = 1 :=
  eq_one_of_isIdT (Rep.powT (by norm_num) rep_ay 23) actionFacts.ay_pow

theorem ay_ne_one :
    a * y ≠ 1 := ne_one_of_isIdT rep_ay actionFacts.ay_ne

theorem orderOf_a : orderOf a = 2 := orderOf_eq_prime a_sq a_ne_one

theorem orderOf_y : orderOf y = 17 := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  exact orderOf_eq_prime y_pow y_ne_one

theorem orderOf_ay : orderOf (a * y) = 23 := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  exact orderOf_eq_prime ay_pow ay_ne_one

theorem isSimpleGroup_J : IsSimpleGroup J := by
  have := isPreprimitive
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Fin 31671) ?_ a y closure_a_y root
    ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  · rw [orderOf_a, orderOf_y]; norm_num
  · rw [orderOf_ay, card_stabilizer_root]; norm_num

theorem card_J : Nat.card J = 4089470473293004800 := by
  rw [← card_lvl_zero, lvl_zero, Subgroup.card_top]

theorem isSimpleGroup_Fi23 :
    IsSimpleGroup Blueprint.NativeSporadic.Fi23 :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J fi23EquivJ

theorem card_Fi23 :
    Nat.card Blueprint.NativeSporadic.Fi23 = 4089470473293004800 := by
  rw [Nat.card_congr fi23EquivJ.toEquiv, card_J]

end CFSG.Sporadic.Fi23
