
module

public import CFSG.Sporadic.ON.ChainBase

public import CFSG.Sporadic.ON.Action
public import CFSG.Sporadic.HS.Chain
public import CFSG.Perm.ChainComplete

public section

namespace CFSG.Sporadic.ON

open Native Matrix
open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.SmallF2.Native (lettersOf instrLt ordOK inTreeB labelsOf)

theorem chain_parts :
    (∀ ins ∈ prog, instrLt nregs ins = true) ∧ slp.2 = true ∧
    (∀ j < sel.size, sel[j]! < nregs) ∧ invOK nPts orb.alpha (invT nPts orb.alpha) = true ∧
    invOK nPts orb.beta (invT nPts orb.beta) = true ∧
    chainOK nPts letters chainBase chainQ chainQb trees 3 = true ∧ orbitSizes trees = orbSizes ∧
    sift trees letters chainQb chainQ 0 (apT orb.alpha chainQ) = true ∧
    sift trees letters chainQb chainQ 0 (apT orb.beta chainQ) = true ∧
    sift trees letters chainQb chainQ 0 (apT negT chainQ) = false := by
  have h := facts.chain
  unfold chainChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨List.all_eq_true.1 h1, h2, fun j hj => ?_, h4, h5, h6, h7, h8, h9, h10⟩
  rw [Array.all_eq_true] at h3
  rw [getElem!_pos sel j hj]
  simpa using h3 j hj

@[expose] noncomputable def genG (z : ℤ) : J :=
  if z = 1 then ga else if z = -1 then ga⁻¹ else if z = 2 then gb else gb⁻¹

theorem rep_genT (z : ℤ) : Rep nPts (genT orb z) (genG z) := by
  unfold genT genG
  split_ifs
  · exact rep_ga
  · exact Rep.inv_of_invOK rep_ga chain_parts.2.2.2.1
  · exact rep_gb
  · exact Rep.inv_of_invOK rep_gb chain_parts.2.2.2.2.1

@[expose] noncomputable def a : J := wordG genG wordA

@[expose] noncomputable def b : J := wordG genG wordB

theorem a_eq : a = ga := by
  simp [a, wordG, wordA, genG]

theorem b_eq : b = gb * ga * gb := by
  simp [b, wordG, wordB, genG, mul_assoc]

theorem rep_a : Rep nPts (wordT nPts (genT orb) wordA) a :=
  Rep.wordT nPts_lt _ fun l _ => rep_genT l

theorem rep_b : Rep nPts (wordT nPts (genT orb) wordB) b :=
  Rep.wordT nPts_lt _ fun l _ => rep_genT l

@[expose] noncomputable def regsG
    (r : ℕ) : J := if r = 0 then a else if r = 1 then b else 1

@[expose] noncomputable def gs
    (j : ℕ) : J := runSLPG prog regsG sel[j]!

theorem rep_regsT :
    ∀ r < regsT.size, Rep nPts regsT[r]! (regsG r) := by
  intro r hr
  rw [regsT_size] at hr
  rw [regsT_get hr]
  unfold regsG
  split_ifs
  · exact rep_a
  · exact rep_b
  · exact Rep.idT nPts_lt

theorem rep_regsT_zero : Rep nPts regsT[0]! a := by
  have := rep_regsT 0 (by rw [regsT_size]; decide)
  simpa [regsG] using this

theorem rep_regsT_one : Rep nPts regsT[1]! b := by
  have := rep_regsT 1 (by rw [regsT_size]; decide)
  simpa [regsG] using this

theorem rep_slp :
    ∀ r < regsT.size, Rep nPts slp.1[r]! (runSLPG prog regsG r) :=
  (runSLP_rep nPts_lt prog regsT regsG
    (fun ins hins => by
      rw [regsT_size]
      exact CFSG.Sporadic.SmallF2.instrRegsLt_of_instrLt (chain_parts.1 ins hins))
    rep_regsT chain_parts.2.1).2

theorem rep_letters :
    ∀ j < letters.size / 2, Rep nPts letters[2 * j]! (gs j) := by
  intro j hj
  rw [letters_size] at hj
  have hj' : j < sel.size := by omega
  have e : letters[2 * j]! = slp.1[sel[j]!]! := by
    rw [getElem!_pos letters (2 * j) (by rw [letters_size]; omega)]
    simp only [letters, lettersOf, Array.getElem_ofFn]
    rw [ite_eq_left (by omega), show 2 * j / 2 = j by omega]
  rw [e]
  exact rep_slp _ (by rw [regsT_size]; exact chain_parts.2.2.1 j hj')

noncomputable abbrev lvl
    (i : ℕ) : Subgroup J := levelGroup letters chainBase (pairG gs) i

theorem chain_ok :
    chainOK nPts letters chainBase chainQ chainQb trees 3 = true :=
  chain_parts.2.2.2.2.2.1

theorem chain_facts' :
    (∀ i < chainBase.size, TreeFacts nPts trees[i]! (levelLetters letters chainBase i)
      (pairG gs) chainBase[i]!) ∧
      (∀ i < chainBase.size, ∀ g ∈ lvl i, idx nPts g chainBase[i]! = chainBase[i]! ↔
        g ∈ lvl (i + 1)) ∧
      ∀ i ≤ chainBase.size, Nat.card (lvl i) =
        ∏ l ∈ Finset.Ico i chainBase.size, trees[l]!.pts.size :=
  chain_facts rep_letters sep chain_ok

theorem tree_size_of
    {l v : ℕ} (hv : orbSizes[l]? = some v) : trees[l]!.pts.size = v := by
  have h := congrArg (fun L : List ℕ => L[l]?) chain_parts.2.2.2.2.2.2.1
  simp only [orbitSizes, List.getElem?_map, Array.getElem?_toList] at h
  rw [hv] at h
  have hl : l < trees.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at h
    simp at h
  rw [Array.getElem?_eq_getElem hl] at h
  simp only [Option.map_some, Option.some.injEq] at h
  rw [getElem!_pos trees l hl]
  exact h

theorem card_lvl_one : Nat.card (lvl 1) = 1876896 := by
  rw [chain_facts'.2.2 1 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 1 3, trees[l]!.pts.size = orbSizes.getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem card_lvl_zero : Nat.card (lvl 0) = 460815505920 := by
  rw [chain_facts'.2.2 0 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 0 3, trees[l]!.pts.size = orbSizes.getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem chainQ_lt'
    {t : ℕ} (ht : t < chainQ.size) : chainQ[t]! < nPts := chainQ_lt ht

theorem ga_mem_lvl : ga ∈ lvl 0 := by
  refine chain_sift_mem rep_letters sep chain_ok (img := apT orb.alpha chainQ) (apT_size _ _)
    (fun t ht => ?_) chain_parts.2.2.2.2.2.2.2.1
  rw [apT_get _ _ ht, rep_ga _ (chainQ_lt ht)]

theorem gb_mem_lvl : gb ∈ lvl 0 := by
  refine chain_sift_mem rep_letters sep chain_ok (img := apT orb.beta chainQ) (apT_size _ _)
    (fun t ht => ?_) chain_parts.2.2.2.2.2.2.2.2.1
  rw [apT_get _ _ ht, rep_gb _ (chainQ_lt ht)]

theorem lvl_zero : lvl 0 = ⊤ := by
  rw [eq_top_iff, ← closure_gab, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ga_mem_lvl
  · exact gb_mem_lvl

theorem mem_lvl_zero (g : J) : g ∈ lvl 0 := by rw [lvl_zero]; trivial

theorem regsG_mem
    (r : ℕ) : regsG r ∈ Subgroup.closure ({a, b} : Set J) := by
  unfold regsG
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · exact Subgroup.one_mem _

theorem gs_mem (j : ℕ) : gs j ∈ Subgroup.closure ({a, b} : Set J) :=
  CFSG.Sporadic.SmallF2.runSLPG_mem _ prog regsG regsG_mem _

theorem lvl_zero_le : lvl 0 ≤ Subgroup.closure ({a, b} : Set J) := by
  unfold lvl levelGroup lettersGroup
  rw [Subgroup.closure_le]
  rintro _ ⟨l, -, rfl⟩
  unfold pairG
  split_ifs
  · exact gs_mem _
  · exact Subgroup.inv_mem _ (gs_mem _)

theorem closure_ab : Subgroup.closure ({a, b} : Set J) = ⊤ := by
  rw [eq_top_iff, ← lvl_zero]
  exact lvl_zero_le

theorem card_J : Nat.card J = 460815505920 := by
  rw [← card_lvl_zero, lvl_zero, Subgroup.card_top]

theorem mat_ne_neg_one (g : J) : mat g ≠ -1 := by
  intro hg
  have hrep := rep_neg hg
  refine not_mem_levelGroup_of_sift_eq_false rep_letters sep chain_ok (g := g)
    (img := apT negT chainQ) (apT_size _ _) (fun t ht => ?_) chain_parts.2.2.2.2.2.2.2.2.2
    (mem_lvl_zero g)
  rw [apT_get _ _ ht, hrep _ (chainQ_lt ht)]

theorem lvl_one_iff (g : J) : idx nPts g 0 = 0 ↔ g ∈ lvl 1 := by
  have := chain_facts'.2.1 0 (by rw [chainBase_size]; norm_num) g (mem_lvl_zero g)
  rwa [chainBase_zero] at this

theorem stabilizer_root : MulAction.stabilizer J root = lvl 1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← lvl_one_iff, idx_of_lt g (by norm_num : 0 < nPts)]
  constructor
  · intro h; rw [h]
  · intro h; exact Fin.ext h

theorem lvl_one_fix {g : J} (hg : g ∈ lvl 1) : g • root = root := by
  rw [← MulAction.mem_stabilizer_iff, stabilizer_root]; exact hg

theorem treeFacts_zero :
    TreeFacts nPts trees[0]! (levelLetters letters chainBase 0)
    (pairG gs) 0 := by
  have := chain_facts'.1 0 (by rw [chainBase_size]; norm_num)
  rwa [chainBase_zero] at this

instance isPretransitive :
    MulAction.IsPretransitive J (Fin nPts) := by
  have hT := treeFacts_zero
  have hcard := hT.card_orbit
  rw [tree_size_of (l := 0) rfl] at hcard
  set Orb := MulAction.orbit (lettersGroup (levelLetters letters chainBase 0) (pairG gs))
    (⟨0, hT.r_lt⟩ : Fin nPts) with hOrb
  have huniv : Orb = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
  have hreach : ∀ p : Fin nPts, ∃ g : J, g • root = p := by
    intro p
    have hp : p ∈ Orb := by rw [huniv]; trivial
    obtain ⟨⟨g, _⟩, hg⟩ := hp
    exact ⟨g, hg⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, hg⟩ := hreach p
  obtain ⟨h, hh⟩ := hreach q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

end CFSG.Sporadic.ON
