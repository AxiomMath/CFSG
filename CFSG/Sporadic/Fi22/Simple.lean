module

public import CFSG.Sporadic.Fi22.Class
public import CFSG.Perm.ChainSpec

public section

namespace CFSG.Sporadic.Fi22

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem zmod3_pow77 : ∀ c : ZMod 3, c ^ 77 = 1 → c = 1 := by decide

theorem commute_of_idx_fix
    {g : J} {r : ℕ} (hr : r < 3510) (h : idx 3510 g r = r) :
    mat g * toMat 77 orb.keys[r]! = toMat 77 orb.keys[r]! * mat g := by
  have e := (idx_eq_iff hr hr).1 h
  have e2 : g * conjPt r = conjPt r * g := by
    calc g * conjPt r = g * conjPt r * g⁻¹ * g := by rw [inv_mul_cancel_right]
      _ = conjPt r * g := by rw [e]
  have hr' : r < orb.keys.size := by rw [orb_size]; exact hr
  rw [← conjPt_mat r hr', ← mat_mul, ← mat_mul, e2]

theorem sep
    (g : J) (hg : ∀ t < chainQ.size, idx 3510 g chainQ[t]! = chainQ[t]!) : g = 1 := by
  have hsep := actionChecks_parts.2.2.2.2.2.1
  have hlt := actionChecks_parts.2.2.2.2.2.2.1
  obtain ⟨c, hc⟩ := scalar_of_sepOK hsep (mat g) (fun i hi => by
    have hi' : i < sepIdx.size := by simpa using hi
    have hr : sepIdx[i]! < 3510 := by
      rw [getElem!_pos sepIdx i hi']
      exact hlt _ (Array.getElem_mem hi')
    have e : (sepIdx.map fun r => orb.keys[r]!)[i]! = orb.keys[sepIdx[i]!]! := by
      rw [getElem!_pos _ i hi, Array.getElem_map, getElem!_pos sepIdx i hi']
    rw [e]
    exact commute_of_idx_fix hr (hg i hi'))
  have hdet := det_eq_one g
  change (mat g).det = 1 at hdet
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc1 := zmod3_pow77 c hdet
  apply mat_injective
  rw [hc, hc1, one_smul]
  rfl

theorem eq_one_of_fix_all
    {g : J} (h : ∀ i : Fin 3510, g • i = i) : g = 1 := by
  apply sep
  intro t ht
  have hQ : chainQ[t]! < 3510 := by
    have hlt := actionChecks_parts.2.2.2.2.2.2.1
    have ht' : t < sepIdx.size := ht
    show sepIdx[t]! < 3510
    rw [getElem!_pos sepIdx t ht']
    exact hlt _ (Array.getElem_mem ht')
  rw [idx_of_lt g hQ, h]

instance faithful : FaithfulSMul J (Fin 3510) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := eq_one_of_fix_all fun i => by rw [mul_smul, hgh, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

@[expose] noncomputable def genG (z : ℤ) : J :=
  if z = 1 then a else if z = -1 then a⁻¹ else if z = 2 then b else b⁻¹

theorem rep_gen (z : ℤ) : Rep 3510 (genTables orb z) (genG z) := by
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
        exact Rep.inv_of_invOK rep_beta actionChecks_parts.2.2.2.2.1

@[expose] noncomputable def gs
    (j : ℕ) : J := wordG genG chainWords[j]!

theorem chainLetters_size : (chainLetters orb).size = 2 * chainWords.size := by
  unfold chainLetters buildLetters; simp

theorem chainLetters_even {j : ℕ} (hj : j < chainWords.size) :
    (chainLetters orb)[2 * j]! = wordT 3510 (genTables orb) chainWords[j]! := by
  unfold chainLetters buildLetters
  rw [getElem!_pos _ (2 * j) (by simp; omega), Array.getElem_ofFn]
  simp only
  rw [ite_eq_left (by omega)]
  congr 2
  omega

theorem rep_letters :
    ∀ j < (chainLetters orb).size / 2, Rep 3510 (chainLetters orb)[2 * j]! (gs j) := by
  intro j hj
  rw [chainLetters_size] at hj
  have hj' : j < chainWords.size := by omega
  rw [chainLetters_even hj']
  exact Rep.wordT (by norm_num) _ fun l _ => rep_gen l

noncomputable abbrev trees : Array Tree := chainTrees 3510 (chainLetters orb) chainBase

noncomputable abbrev lvl (i : ℕ) : Subgroup J :=
  levelGroup (chainLetters orb) chainBase (pairG gs) i

theorem chain_facts' :
    (∀ i < chainBase.size, TreeFacts 3510 trees[i]! (levelLetters (chainLetters orb) chainBase i)
      (pairG gs) chainBase[i]!) ∧
      (∀ i < chainBase.size, ∀ g ∈ lvl i, idx 3510 g chainBase[i]! = chainBase[i]! ↔
        g ∈ lvl (i + 1)) ∧
      ∀ i ≤ chainBase.size, Nat.card (lvl i) =
        ∏ l ∈ Finset.Ico i chainBase.size, trees[l]!.pts.size :=
  chain_facts rep_letters sep actionChecks_parts.2.2.2.2.2.2.2.1

theorem chainBase_size : chainBase.size = 5 := rfl

theorem tree_size_of
    {l v : ℕ} (hv : [3510, 2816, 1680, 108, 36][l]? = some v) :
    trees[l]!.pts.size = v := by
  have h := actionChecks_parts.2.2.2.2.2.2.2.2.1
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

theorem card_lvl_one : Nat.card (lvl 1) = 18393661440 := by
  rw [chain_facts'.2.2 1 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 1 5, trees[l]!.pts.size =
      [3510, 2816, 1680, 108, 36].getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem card_lvl_zero : Nat.card (lvl 0) = 64561751654400 := by
  rw [chain_facts'.2.2 0 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 0 5, trees[l]!.pts.size =
      [3510, 2816, 1680, 108, 36].getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem chainWords_zero : chainWords[0]! = [1] := by decide

theorem chainWords_one : chainWords[1]! = [2] := by decide

theorem chainWords_size : chainWords.size = 16 := by decide

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

noncomputable abbrev root : Fin 3510 := ⟨0, by norm_num⟩

theorem lvl_one_iff (g : J) : idx 3510 g 0 = 0 ↔ g ∈ lvl 1 := by
  have := chain_facts'.2.1 0 (by rw [chainBase_size]; norm_num) g (mem_lvl_zero g)
  rwa [chainBase_zero] at this

theorem stabilizer_root : MulAction.stabilizer J root = lvl 1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← lvl_one_iff, idx_of_lt g (by norm_num : 0 < 3510)]
  constructor
  · intro h; rw [h]
  · intro h; exact Fin.ext h

theorem card_stabilizer_root :
    Nat.card (MulAction.stabilizer J root) = 18393661440 := by
  rw [stabilizer_root]; exact card_lvl_one

theorem lvl_one_fix {g : J} (hg : g ∈ lvl 1) : g • root = root := by
  rw [← MulAction.mem_stabilizer_iff, stabilizer_root]; exact hg

theorem treeFacts_zero :
    TreeFacts 3510 trees[0]! (levelLetters (chainLetters orb) chainBase 0)
    (pairG gs) 0 := by
  have := chain_facts'.1 0 (by rw [chainBase_size]; norm_num)
  rwa [chainBase_zero] at this

instance isPretransitive :
    MulAction.IsPretransitive J (Fin 3510) := by
  have hT := treeFacts_zero
  have hcard := hT.card_orbit
  rw [tree_size_of (l := 0) rfl] at hcard
  set O := MulAction.orbit (lettersGroup (levelLetters (chainLetters orb) chainBase 0) (pairG gs))
    (⟨0, hT.r_lt⟩ : Fin 3510) with hO
  have huniv : O = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
  have hreach : ∀ p : Fin 3510, ∃ g : J, g • root = p := by
    intro p
    have hp : p ∈ O := by rw [huniv]; trivial
    obtain ⟨⟨g, _⟩, hg⟩ := hp
    exact ⟨g, hg⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, hg⟩ := hreach p
  obtain ⟨h, hh⟩ := hreach q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

noncomputable abbrev lv1 : Array ℕ := levelLetters (chainLetters orb) chainBase 1

noncomputable abbrev T2 : Tree := treeBFS 3510 subRoot (chainLetters orb) lv1

theorem rep_pairG_all :
    ∀ l < (chainLetters orb).size, Rep 3510 (chainLetters orb)[l]! (pairG gs l) :=
  rep_pairG rep_letters (by rw [chainLetters_size]; omega) (chainOK_parts
    actionChecks_parts.2.2.2.2.2.2.2.1).2.1

theorem treeFacts_one :
    TreeFacts 3510 trees[1]! lv1 (pairG gs) 1 := by
  have := chain_facts'.1 1 (by rw [chainBase_size]; norm_num)
  rwa [chainBase_one] at this

theorem treeFacts_two : TreeFacts 3510 T2 lv1 (pairG gs) subRoot :=
  treeOK_facts (fun l hl => rep_pairG_all l (levelLetters_lt hl))
    actionChecks_parts.2.2.2.2.2.2.2.2.2.1

theorem lvl_one_eq : lettersGroup lv1 (pairG gs) = lvl 1 := rfl

theorem T2_size :
    T2.pts.size = 693 := actionChecks_parts.2.2.2.2.2.2.2.2.2.2.1

@[expose] def InTree (T : Tree) (p : ℕ) : Prop :=
  ap T.pos p < T.pts.size ∧ ap T.pts (ap T.pos p) = p

instance (T : Tree) (p : ℕ) : Decidable (InTree T p) := by unfold InTree; infer_instance

theorem inTree_iff
    {T : Tree} {lv : Array ℕ} {r : ℕ} (hT : TreeFacts 3510 T lv (pairG gs) r)
    (p : Fin 3510) :
    InTree T p.val ↔
      p ∈ MulAction.orbit (lettersGroup lv (pairG gs)) (⟨r, hT.r_lt⟩ : Fin 3510) := by
  rw [hT.mem_orbit_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, h2⟩
  · rintro ⟨k, hk, hkp⟩
    refine ⟨?_, ?_⟩
    · rw [← hkp, hT.pos_pts k hk]; exact hk
    · rw [← hkp, hT.pos_pts k hk]

@[expose] noncomputable def subLab (p : Fin 3510) : Fin 3 :=
  if p.val = 0 then 0 else if InTree trees[1]! p.val then 1 else 2

theorem orbit_smul_mem
    {H : Subgroup J} {x p : Fin 3510} (h : J) (hh : h ∈ H)
    (hp : p ∈ MulAction.orbit H x) : h • p ∈ MulAction.orbit H x := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := hp
  refine ⟨⟨h * k, H.mul_mem hh hk⟩, ?_⟩
  show (h * k) • x = h • (k • x)
  exact mul_smul h k x

theorem inTree_one (p : Fin 3510) :
    InTree trees[1]! p.val ↔ p ∈ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 3510) :=
  inTree_iff treeFacts_one p

theorem inTree_two (p : Fin 3510) :
    InTree T2 p.val ↔
      p ∈ MulAction.orbit (lvl 1) (⟨subRoot, treeFacts_two.r_lt⟩ : Fin 3510) :=
  inTree_iff treeFacts_two p

theorem orbit_one_ne_zero (p : Fin 3510)
    (hp : p ∈ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 3510)) : p.val ≠ 0 := by
  intro h0
  obtain ⟨⟨k, hk⟩, hkp⟩ := hp
  have hp0 : p = root := Fin.ext h0
  have : (k⁻¹ : J) • p = (⟨1, treeFacts_one.r_lt⟩ : Fin 3510) := by
    rw [← hkp]
    exact inv_smul_smul k _
  rw [hp0, lvl_one_fix ((lvl 1).inv_mem hk)] at this
  exact absurd (Fin.mk.inj this) (by decide)

theorem subLab_eq_zero {p : Fin 3510} : subLab p = 0 ↔ p = root := by
  unfold subLab
  constructor
  · intro h
    by_contra hp
    have hp' : p.val ≠ 0 := fun e => hp (Fin.ext e)
    rw [ite_eq_right hp'] at h
    split_ifs at h <;> exact absurd h (by decide)
  · rintro rfl; simp

theorem subLab_eq_one {p : Fin 3510} :
    subLab p = 1 ↔ p ∈ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 3510) := by
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

theorem subLab_eq_two {p : Fin 3510} :
    subLab p = 2 ↔ p ≠ root ∧ p ∉ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 3510) := by
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

theorem two_mem_orbit {p : Fin 3510} (h : subLab p = 2) :
    p ∈ MulAction.orbit (lvl 1) (⟨subRoot, treeFacts_two.r_lt⟩ : Fin 3510) := by
  obtain ⟨h0, h1⟩ := subLab_eq_two.1 h
  rw [← inTree_one p] at h1
  rcases actionChecks_parts.2.2.2.2.2.2.2.2.2.2.2 p.val p.isLt with hc | hc | hc
  · exact absurd (Fin.ext hc) h0
  · exact absurd hc h1
  · exact (inTree_two p).1 ⟨by rw [T2_size]; exact hc.1, hc.2⟩

theorem subLab_inv :
    ∀ h ∈ lvl 1, ∀ p : Fin 3510, subLab (h • p) = subLab p := by
  intro h hh p
  have hinv : h⁻¹ ∈ lvl 1 := (lvl 1).inv_mem hh
  by_cases hp0 : p = root
  · rw [hp0, lvl_one_fix hh]
  by_cases hp1 : p ∈ MulAction.orbit (lvl 1) (⟨1, treeFacts_one.r_lt⟩ : Fin 3510)
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
    ∀ p q : Fin 3510, subLab p = subLab q → ∃ h ∈ lvl 1, h • p = q := by
  intro p q hpq
  have key : ∀ {x : Fin 3510} {H : Subgroup J}, p ∈ MulAction.orbit H x →
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
    (Finset.univ.filter (fun p : Fin 3510 => subLab p = 1)).card = 2816 := by
  classical
  have hc := treeFacts_one.card_orbit
  rw [tree_size_of (l := 1) rfl] at hc
  have hset : MulAction.orbit (lettersGroup lv1 (pairG gs)) (⟨1, treeFacts_one.r_lt⟩ : Fin 3510) =
      ↑(Finset.univ.filter (fun p : Fin 3510 => subLab p = 1)) := by
    ext p
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    exact subLab_eq_one.symm
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
  exact hc

theorem card_subLab_zero :
    (Finset.univ.filter (fun p : Fin 3510 => subLab p = 0)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨root, ?_⟩
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact subLab_eq_zero

theorem card_subLab_two :
    (Finset.univ.filter (fun p : Fin 3510 => subLab p = 2)).card = 693 := by
  have h := Finset.card_eq_sum_card_fiberwise (f := subLab) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h0 : (Finset.univ.filter (fun p : Fin 3510 => subLab p = 0)).card = 1 := card_subLab_zero
  have h1 : (Finset.univ.filter (fun p : Fin 3510 => subLab p = 1)).card = 2816 := card_subLab_one
  have key : ∀ f : Fin 3 → ℕ, 3510 = ∑ i, f i → f 0 = 1 → f 1 = 2816 → f 2 = 693 := by
    intro f h h0 h1
    rw [Fin.sum_univ_three] at h
    omega
  exact key (fun i => (Finset.univ.filter (fun p : Fin 3510 => subLab p = i)).card) h h0 h1

@[expose] def subSizes : Fin 3 → ℕ := ![1, 2816, 693]

theorem subSizes_blocks : ∀ S : Finset (Fin 3), (0 : Fin 3) ∈ S →
    (∑ i ∈ S, subSizes i) ∣ 3510 → S = {0} ∨ S = Finset.univ := by
  decide

theorem card_subLab (i : Fin 3) :
    (Finset.univ.filter (fun p : Fin 3510 => subLab p = i)).card = subSizes i := by
  fin_cases i
  · exact card_subLab_zero
  · exact card_subLab_one
  · exact card_subLab_two

theorem isPreprimitive : MulAction.IsPreprimitive J (Fin 3510) := by
  apply isPreprimitive_of_suborbit_labels root (lvl 1) (fun h hh => lvl_one_fix hh) subLab
    subLab_inv subLab_orb
  intro S hS hdvd
  have h0 : subLab root = 0 := subLab_eq_zero.2 rfl
  rw [h0] at hS ⊢
  have hsum : (∑ i ∈ S, (Finset.univ.filter (fun p : Fin 3510 => subLab p = i)).card) =
      ∑ i ∈ S, subSizes i := Finset.sum_congr rfl fun i _ => card_subLab i
  rw [hsum, Fintype.card_fin] at hdvd
  exact subSizes_blocks S hS hdvd

theorem mat_pow (g : J) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  simp [mat, Units.val_pow_eq_pow_val]

theorem mat_one : mat (1 : J) = 1 := rfl

theorem a_sq : a ^ 2 = 1 := by
  apply mat_injective
  rw [mat_pow, mat_one, mat_a, toMat_matA, pow_two]
  exact matrixFacts.A_sq

theorem a_ne_one : a ≠ 1 := by
  intro h
  apply matrixFacts.A_ne
  have := congrArg mat h
  rwa [mat_a, toMat_matA, mat_one] at this

theorem b_pow : b ^ 13 = 1 := by
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

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

theorem orderOf_a : orderOf a = 2 := orderOf_eq_prime a_sq a_ne_one

theorem orderOf_ab :
    orderOf (a * b) = 11 := orderOf_eq_prime ab_pow ab_ne_one

theorem orderOf_b : orderOf b = 13 := orderOf_eq_prime b_pow b_ne_one

theorem a_mul_ab : a * (a * b) = b := by
  rw [← mul_assoc, ← pow_two, a_sq, one_mul]

theorem closure_a_ab :
    Subgroup.closure ({a, a * b} : Set J) = ⊤ := by
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  have ha : a ∈ Subgroup.closure ({a, a * b} : Set J) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hab : a * b ∈ Subgroup.closure ({a, a * b} : Set J) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  rintro _ (rfl | rfl)
  · exact ha
  · have := Subgroup.mul_mem _ ha hab
    rwa [a_mul_ab] at this

theorem isSimpleGroup_J : IsSimpleGroup J := by
  have := isPreprimitive
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Fin 3510) ?_ a (a * b) closure_a_ab root
    ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  · rw [orderOf_a, orderOf_ab]; norm_num
  · rw [a_mul_ab, orderOf_b, card_stabilizer_root]; norm_num

theorem card_J : Nat.card J = 64561751654400 := by
  rw [← card_lvl_zero, lvl_zero, Subgroup.card_top]

theorem isSimpleGroup_Fi22 :
    IsSimpleGroup Blueprint.NativeSporadic.Fi22 :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J fi22EquivJ

theorem card_Fi22 :
    Nat.card Blueprint.NativeSporadic.Fi22 = 64561751654400 := by
  rw [Nat.card_congr fi22EquivJ.toEquiv, card_J]

end CFSG.Sporadic.Fi22
