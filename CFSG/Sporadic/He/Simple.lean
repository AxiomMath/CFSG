module

public import CFSG.Sporadic.He.Action
public import CFSG.Sporadic.He.Primitive
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.Fi23.SlpSpec

public section

namespace CFSG.Sporadic.He

open Native Matrix
open CFSG.Sporadic.Th CFSG.Perm
open CFSG.Sporadic.Th.Native (Table ap compT powT invT invOK invoOK wordT)
open CFSG.Perm.Native (Tree treeBFS treeOK chainOK chainTrees levelLetters orbitSizes)
open CFSG.Sporadic.Fi23 (slpG slpG_eq slpInv_full rep_slpLetters)

theorem a_mul_self : a * a = 1 := by
  apply mat_injective
  rw [mat_mul, mat_a, mat_one]
  exact mA_sq

theorem a_inv : a⁻¹ = a := by
  rw [inv_eq_iff_mul_eq_one]
  exact a_mul_self

@[expose] noncomputable def genG (z : ℤ) : J :=
  if z = 1 then a else if z = -1 then a⁻¹ else if z = 2 then b else b⁻¹

theorem rep_gen (z : ℤ) : Rep 8330 (genTables orb z) (genG z) := by
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
  (slpInv_full (n := 8330) (gens := genTables orb) actionFacts.slp_ok).1

theorem rep_letters :
    ∀ j < letters.size / 2, Rep 8330 letters[2 * j]! (gs j) := by
  intro j hj
  rw [letters_size] at hj
  have hinv := (chainOK_parts actionFacts.chain).2.1
  refine rep_slpLetters (by norm_num) rep_gen actionFacts.slp_ok (fun i hi => ?_) j
    (by omega)
  exact hinv i (by rw [letters_size]; omega)

noncomputable abbrev lvl
    (i : ℕ) : Subgroup J := levelGroup letters chainBase (pairG gs) i

theorem chain_facts' :
    (∀ i < chainBase.size, TreeFacts 8330 trees[i]! (levelLetters letters chainBase i)
      (pairG gs) chainBase[i]!) ∧
      (∀ i < chainBase.size, ∀ g ∈ lvl i, idx 8330 g chainBase[i]! = chainBase[i]! ↔
        g ∈ lvl (i + 1)) ∧
      ∀ i ≤ chainBase.size, Nat.card (lvl i) =
        ∏ l ∈ Finset.Ico i chainBase.size, trees[l]!.pts.size :=
  chain_facts rep_letters sep actionFacts.chain

theorem chainBase_size : chainBase.size = 5 := rfl

theorem tree_size_of
    {l v : ℕ} (hv : [8330, 4480, 27, 2, 2][l]? = some v) :
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

theorem card_lvl_one : Nat.card (lvl 1) = 483840 := by
  rw [chain_facts'.2.2 1 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 1 5, trees[l]!.pts.size =
      [8330, 4480, 27, 2, 2].getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem card_lvl_zero : Nat.card (lvl 0) = 4030387200 := by
  rw [chain_facts'.2.2 0 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 0 5, trees[l]!.pts.size =
      [8330, 4480, 27, 2, 2].getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem chainBase_zero : chainBase[0]! = 0 := rfl

theorem chainWords_size : chainWords.size = 8 := rfl

theorem gs_zero : gs 0 = a := by
  rw [gs, slpG_eq, actionFacts.word0]
  simp [wordG, genG]

theorem gs_one : gs 1 = b := by
  rw [gs, slpG_eq, actionFacts.word1]
  simp [wordG, genG]

theorem lvl_zero : lvl 0 = ⊤ := by
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  have hsz : 2 < letters.size := by rw [letters_size, chainWords_size]; decide
  rintro _ (rfl | rfl)
  · have : pairG gs 0 = a := by simp [pairG, gs_zero]
    rw [← this]
    exact lG_mem (mem_levelLetters_zero.2 (by omega))
  · have : pairG gs 2 = b := by simp [pairG, gs_one]
    rw [← this]
    exact lG_mem (mem_levelLetters_zero.2 hsz)

theorem mem_lvl_zero (g : J) : g ∈ lvl 0 := by rw [lvl_zero]; trivial

noncomputable abbrev root : Fin 8330 := ⟨0, by norm_num⟩

theorem lvl_one_iff (g : J) : idx 8330 g 0 = 0 ↔ g ∈ lvl 1 := by
  have := chain_facts'.2.1 0 (by rw [chainBase_size]; norm_num) g (mem_lvl_zero g)
  rwa [chainBase_zero] at this

theorem stabilizer_root : MulAction.stabilizer J root = lvl 1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← lvl_one_iff, idx_of_lt g (by norm_num : 0 < 8330)]
  constructor
  · intro h; rw [h]
  · intro h; exact Fin.ext h

theorem card_stabilizer_root :
    Nat.card (MulAction.stabilizer J root) = 483840 := by
  rw [stabilizer_root]; exact card_lvl_one

theorem lvl_one_fix {g : J} (hg : g ∈ lvl 1) : g • root = root := by
  rw [← MulAction.mem_stabilizer_iff, stabilizer_root]; exact hg

theorem treeFacts_zero :
    TreeFacts 8330 trees[0]! (levelLetters letters chainBase 0)
    (pairG gs) 0 := by
  have := chain_facts'.1 0 (by rw [chainBase_size]; norm_num)
  rwa [chainBase_zero] at this

instance isPretransitive :
    MulAction.IsPretransitive J (Fin 8330) := by
  have hT := treeFacts_zero
  have hcard := hT.card_orbit
  rw [tree_size_of (l := 0) rfl] at hcard
  set O := MulAction.orbit (lettersGroup (levelLetters letters chainBase 0) (pairG gs))
    (⟨0, hT.r_lt⟩ : Fin 8330) with hO
  have huniv : O = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
  have hreach : ∀ p : Fin 8330, ∃ g : J, g • root = p := by
    intro p
    have hp : p ∈ O := by rw [huniv]; trivial
    obtain ⟨⟨g, _⟩, hg⟩ := hp
    exact ⟨g, hg⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, hg⟩ := hreach p
  obtain ⟨h, hh⟩ := hreach q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

theorem rep_pairG_all :
    ∀ l < letters.size, Rep 8330 letters[l]! (pairG gs l) :=
  rep_pairG rep_letters (by rw [letters_size]; omega) (chainOK_parts actionFacts.chain).2.1

theorem lvl_one_eq : lettersGroup lv1 (pairG gs) = lvl 1 := rfl

theorem sub_parts :
    subTs.size = 7 ∧ subRoots.size = 7 ∧ subRoots[0]! = 0 ∧
    (∀ i < 7, treeOK 8330 subRoots[i]! subTs[i]! letters lv1 = true ∧
      ∀ k < subTs[i]!.pts.size, labs[ap subTs[i]!.pts k]! = i) ∧
    (∀ p < 8330, labs[p]! < 7 ∧ inTreeB subTs[labs[p]!]! p = true) ∧
    (subTs.toList.map fun T => T.pts.size) = subSizes := by
  have h := actionFacts.sub
  unfold subChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_, fun p hp => ?_, h6⟩
  · have := (allIn_eq_true.1 h4) i (Nat.zero_le _) hi
    simp only [Bool.and_eq_true] at this
    refine ⟨this.1, fun k hk => ?_⟩
    have := (allIn_eq_true.1 this.2) k (Nat.zero_le _) hk
    simpa using this
  · have := (allIn_eq_true.1 h5) p (Nat.zero_le _) hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this

theorem subFacts {i : ℕ} (hi : i < 7) :
    TreeFacts 8330 subTs[i]! lv1 (pairG gs) subRoots[i]! :=
  treeOK_facts (fun l hl => rep_pairG_all l (levelLetters_lt hl)) (sub_parts.2.2.2.1 i hi).1

theorem subSize_eq
    {i : ℕ} (hi : i < 7) : subTs[i]!.pts.size = subSizes[i]! := by
  have h := congrArg (fun L : List ℕ => L[i]!) sub_parts.2.2.2.2.2
  have hi' : i < subTs.size := by rw [sub_parts.1]; exact hi
  rw [← h, getElem!_pos (subTs.toList.map fun T => T.pts.size) i (by simp [hi']),
    List.getElem_map, Array.getElem_toList, getElem!_pos subTs i hi']

@[expose] noncomputable def subLab (p : Fin 8330) : Fin 7 :=
  ⟨labs[p.val]!, (sub_parts.2.2.2.2.1 p.val p.isLt).1⟩

theorem subLab_val
    (p : Fin 8330) : (subLab p).val = labs[p.val]! := rfl

theorem subLab_eq_iff (i : Fin 7) (p : Fin 8330) :
    subLab p = i ↔
      p ∈ MulAction.orbit (lvl 1) (⟨subRoots[i.val]!, (subFacts i.isLt).r_lt⟩ : Fin 8330) := by
  rw [← lvl_one_eq, (subFacts i.isLt).mem_orbit_iff]
  constructor
  · intro h
    have hc := (sub_parts.2.2.2.2.1 p.val p.isLt).2
    rw [← subLab_val, h] at hc
    unfold inTreeB at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    exact ⟨_, hc.1, hc.2⟩
  · rintro ⟨k, hk, hkp⟩
    apply Fin.ext
    rw [subLab_val, ← hkp]
    exact (sub_parts.2.2.2.1 i.val i.isLt).2 k hk

theorem exists_of_mem_orbit
    {H : Subgroup J} {x p q : Fin 8330} (hp : p ∈ MulAction.orbit H x)
    (hq : q ∈ MulAction.orbit H x) : ∃ h ∈ H, h • p = q := by
  obtain ⟨⟨u, hu⟩, rfl⟩ := hp
  obtain ⟨⟨v, hv⟩, rfl⟩ := hq
  refine ⟨v * u⁻¹, H.mul_mem hv (H.inv_mem hu), ?_⟩
  show (v * u⁻¹) • (u • x) = v • x
  rw [mul_smul, inv_smul_smul]

theorem subLab_orb :
    ∀ p q : Fin 8330, subLab p = subLab q → ∃ h ∈ lvl 1, h • p = q := by
  intro p q hpq
  exact exists_of_mem_orbit ((subLab_eq_iff (subLab p) p).1 rfl)
    ((subLab_eq_iff (subLab p) q).1 hpq.symm)

theorem card_subLab (i : Fin 7) :
    (Finset.univ.filter (fun p : Fin 8330 => subLab p = i)).card = subSizes[i.val]! := by
  classical
  have hc := (subFacts i.isLt).card_orbit
  rw [subSize_eq i.isLt, lvl_one_eq] at hc
  have hset : MulAction.orbit (lvl 1) (⟨subRoots[i.val]!, (subFacts i.isLt).r_lt⟩ : Fin 8330) =
      ↑(Finset.univ.filter (fun p : Fin 8330 => subLab p = i)) := by
    ext p
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    exact (subLab_eq_iff i p).symm
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
  exact hc

theorem subLab_root : subLab root = 0 := by
  apply Fin.ext
  rw [subLab_val]
  have h0 := (sub_parts.2.2.2.1 0 (by norm_num)).2 0 (subFacts (i := 0) (by norm_num)).size_pos
  rw [(subFacts (i := 0) (by norm_num)).root, sub_parts.2.2.1] at h0
  exact h0

@[expose] def subSizesF : Fin 7 → ℕ := ![1, 4480, 1344, 840, 840, 720, 105]

theorem subSizes_getElem (i : Fin 7) : subSizes[i.val]! = subSizesF i := by
  revert i; decide

set_option maxRecDepth 10000 in
theorem subSizes_blocks : ∀ S : Finset (Fin 7), (0 : Fin 7) ∈ S →
    (∑ i ∈ S, subSizesF i) ∣ 8330 →
      S = {0} ∨ S = Finset.univ ∨ S = {0, 3, 5, 6} ∨ S = {0, 4, 5, 6} := by
  decide

@[expose] noncomputable def wit : J := wordG genG witWord

theorem rep_wit :
    Rep 8330 tabW wit := Rep.wordT (by norm_num) _ fun z _ => rep_gen z

theorem subLab_of_idx
    {g : J} {T : Table} (hT : Rep 8330 T g) {p : ℕ} (hp : p < 8330) :
    (subLab (g • (⟨p, hp⟩ : Fin 8330))).val = labs[ap T p]! := by
  rw [subLab_val, smul_val_eq_idx, ← hT p hp]

theorem subLab_wit_root : subLab (wit • root) = 5 :=
  Fin.ext ((subLab_of_idx rep_wit (by norm_num : 0 < 8330)).trans actionFacts.wit0)

theorem isPreprimitive : MulAction.IsPreprimitive J (Fin 8330) := by
  apply isPreprimitive_of_suborbit_labels_witness root (lvl 1) (fun h hh => lvl_one_fix hh)
    subLab subLab_orb
  intro S hS hdvd
  rw [subLab_root] at hS ⊢
  have hsum : (∑ i ∈ S, (Finset.univ.filter (fun p : Fin 8330 => subLab p = i)).card) =
      ∑ i ∈ S, subSizesF i := Finset.sum_congr rfl fun i _ => by
    rw [card_subLab, subSizes_getElem]
  rw [hsum, Fintype.card_fin] at hdvd
  rcases subSizes_blocks S hS hdvd with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨wit, ⟨21, by norm_num⟩, ?_, ?_, ?_⟩)
    · rw [h, show subLab ⟨21, by norm_num⟩ = 3 from Fin.ext actionFacts.wit1]; decide
    · rw [h, subLab_wit_root]; decide
    · rw [h, show subLab (wit • (⟨21, by norm_num⟩ : Fin 8330)) = 1 from
        Fin.ext ((subLab_of_idx rep_wit (by norm_num : 21 < 8330)).trans actionFacts.wit1')]
      decide
  · refine Or.inr (Or.inr ⟨wit, ⟨24, by norm_num⟩, ?_, ?_, ?_⟩)
    · rw [h, show subLab ⟨24, by norm_num⟩ = 4 from Fin.ext actionFacts.wit2]; decide
    · rw [h, subLab_wit_root]; decide
    · rw [h, show subLab (wit • (⟨24, by norm_num⟩ : Fin 8330)) = 3 from
        Fin.ext ((subLab_of_idx rep_wit (by norm_num : 24 < 8330)).trans actionFacts.wit2')]
      decide

theorem a_sq : a ^ 2 = 1 := by rw [pow_two, a_mul_self]

theorem a_ne_one :
    a ≠ 1 := ne_one_of_isIdT rep_alpha actionFacts.a_ne

theorem b_pow : b ^ 7 = 1 :=
  eq_one_of_isIdT (Rep.powT (by norm_num) rep_beta 7) actionFacts.b_pow

theorem b_ne_one : b ≠ 1 := ne_one_of_isIdT rep_beta actionFacts.b_ne

theorem rep_ab :
    Rep 8330 tabAB (a * b) := Rep.compT rep_alpha rep_beta

theorem ab_pow : (a * b) ^ 17 = 1 :=
  eq_one_of_isIdT (Rep.powT (by norm_num) rep_ab 17) actionFacts.ab_pow

theorem ab_ne_one :
    a * b ≠ 1 := ne_one_of_isIdT rep_ab actionFacts.ab_ne

theorem orderOf_a : orderOf a = 2 := orderOf_eq_prime a_sq a_ne_one

theorem orderOf_b : orderOf b = 7 := orderOf_eq_prime b_pow b_ne_one

theorem orderOf_ab : orderOf (a * b) = 17 := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  exact orderOf_eq_prime ab_pow ab_ne_one

theorem isSimpleGroup_J : IsSimpleGroup J := by
  have := isPreprimitive
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Fin 8330) ?_ a b closure_ab root ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  · rw [orderOf_a, orderOf_b]; norm_num
  · rw [orderOf_ab, card_stabilizer_root]; norm_num

theorem card_J : Nat.card J = 4030387200 := by
  rw [← card_lvl_zero, lvl_zero, Subgroup.card_top]

theorem isSimpleGroup_He :
    IsSimpleGroup Blueprint.NativeSporadic.He :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J heEquivJ

theorem card_He :
    Nat.card Blueprint.NativeSporadic.He = 4030387200 := by
  rw [Nat.card_congr heEquivJ.toEquiv, card_J]

end CFSG.Sporadic.He
