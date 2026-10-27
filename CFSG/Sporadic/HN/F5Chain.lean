module

public import CFSG.Sporadic.HN.F5Group
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Fi23.SlpSpec

public section

namespace CFSG.Sporadic.F5

open Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.LevelChain CFSG.Sporadic.LevelChain.Native CFSG.Sporadic.Fi23
open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.He.Native
open CFSG.Sporadic.SmallF2.Native (labelsOf inTreeB ordOK)

variable (D : F5Data)

noncomputable abbrev L : Array Table := slpLetters D.n (genT D.n (O D)) D.words

noncomputable abbrev T : Array Tree := levelTrees D.n (L D) D.starts D.base

noncomputable abbrev lv1 : Array ℕ := levelLv D.starts 1

noncomputable abbrev S : Array Tree := D.subReps.map fun r => treeBFS D.n r (L D) (lv1 D)

noncomputable abbrev labs : Array ℕ := labelsOf D.n (S D)

structure Facts (c : ℕ) : Prop extends BaseFacts D where
  slp : slpOK D.words = true
  nest : nestOK D.words D.starts = true
  starts_size : D.starts.size = D.base.size + 1
  base_two : 2 ≤ D.base.size
  base0 : D.base[0]! = 0
  chain : levelChainOK D.n (L D) D.starts D.ords D.base D.Q D.qb (T D) c = true
  T0 : (T D)[0]!.pts.size = D.n
  orbSizes : orbitSizes (T D) = D.orbSizes
  k_pos : 0 < D.subReps.size
  rep0 : D.subReps[0]! = 0
  S_size : (S D).size = D.subReps.size
  subSizes : ((S D).toList.map fun T => T.pts.size) = D.subSizes
  subTrees : ∀ j < D.subReps.size, treeOK D.n D.subReps[j]! (S D)[j]! (L D) (lv1 D) = true
  labs_lt : ∀ p < D.n, (labs D)[p]! < D.subReps.size
  labs_mem : ∀ p < D.n, inTreeB (S D)[(labs D)[p]!]! p = true
  labs_pts : ∀ j < D.subReps.size, ∀ t < (S D)[j]!.pts.size, (labs D)[ap (S D)[j]!.pts t]! = j
  div : divOK D.n D.subSizes = true
  ordA : ordOK D.n D.Q (O D).alpha D.ordA = true
  ordB : ordOK D.n D.Q (O D).beta D.ordB = true
  ordC : ordOK D.n D.Q (wordT D.n (genT D.n (O D)) (cWordOf D.gWord)) D.ordC = true

private theorem array_all_lt {a : Array ℕ} {m : ℕ} (h : a.all (· < m) = true) :
    ∀ i < a.size, a[i]! < m := by
  intro i hi
  rw [Array.all_eq_true] at h
  have := h i hi
  rw [getElem!_pos a i hi]
  simpa using this

theorem facts_of_f5Cert {c : ℕ} (h : f5Cert D c = true) : Facts D c := by
  unfold f5Cert matrixChecks orbitChecks chainChecks subChecks ordChecks at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at h
  obtain ⟨hd0, hd, heA, heB, hpA, hpB, horb, hks, has, hbs, hn, hiA, hiB, hQs, hQl, hbas, hslp,
    hnest, hsts, hb2, hb0, hch, hT0, hos, hk, hr0, hSs, hss, htr, hlab, hpts, hdiv, ho0, ho1,
    ho2⟩ := h
  refine ⟨⟨hd0, hd, heA, heB, hpA, hpB, f5OrbitOK_facts horb, hks, has, hbs, hn, hiA, hiB, hQs,
    array_all_lt hQl, hbas⟩, hslp, hnest, hsts, hb2, hb0, hch, hT0, hos, hk, hr0, hSs, hss,
    fun j hj => (allIn_eq_true.1 htr) j (Nat.zero_le _) hj,
    fun p hp => ?_, fun p hp => ?_, fun j hj t ht => ?_, hdiv, ho0, ho1, ho2⟩
  · have := (allIn_eq_true.1 hlab) p (Nat.zero_le _) hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · have := (allIn_eq_true.1 hlab) p (Nat.zero_le _) hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 hpts) j (Nat.zero_le _) hj)) t (Nat.zero_le _) ht
    simpa using this

@[expose] noncomputable def genG (z : ℤ) : J D :=
  if z = 1 then a D else if z = -1 then (a D)⁻¹ else if z = 2 then b D else (b D)⁻¹

@[expose] noncomputable def gs (j : ℕ) : J D := slpG (genG D) D.words j

noncomputable abbrev lvl (i : ℕ) : Subgroup (J D) := lvlGroup D.starts (gs D) i

section Facts

variable {D} {c : ℕ} (hF : Facts D c)
include hF

theorem n_lt_two_pow : D.n < 2 ^ 32 := lt_trans hF.n_lt (by norm_num)

theorem rep_genT (z : ℤ) : Rep D.n (genT D.n (O D) z) (genG D z) := by
  unfold genT genG
  split_ifs
  · exact rep_a hF.toBaseFacts
  · exact Rep.inv_of_invOK (rep_a hF.toBaseFacts) hF.invA
  · exact rep_b hF.toBaseFacts
  · exact Rep.inv_of_invOK (rep_b hF.toBaseFacts) hF.invB

theorem L_size : (L D).size = 2 * D.words.size :=
  (slpInv_full (n := D.n) (gens := genT D.n (O D)) hF.slp).1

theorem rep_letters : ∀ j < (L D).size / 2, Rep D.n (L D)[2 * j]! (gs D j) := by
  intro j hj
  rw [L_size hF] at hj
  have hinv := (levelChainOK_parts hF.chain).2.1
  refine rep_slpLetters (n_lt_two_pow hF) (rep_genT hF) hF.slp (fun i hi => ?_) j (by omega)
  exact hinv i (by rw [L_size hF]; omega)

theorem nest_parts : D.words[0]! = [1] ∧ D.words[1]! = [2] ∧ 2 ≤ D.starts.size ∧
    D.starts[0]! = 0 ∧ D.starts[1]! = 2 ∧ D.words.size = D.starts[D.starts.size - 1]! ∧
    ∀ i, 1 ≤ i → i < D.starts.size - 1 → ∀ j, D.starts[i]! ≤ j → j < D.starts[i + 1]! →
      ∀ z ∈ D.words[j]!, D.starts[i - 1]! + 3 ≤ z.natAbs ∧ z.natAbs < D.starts[i]! + 3 := by
  have h := hF.nest
  unfold nestOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun i hi1 hi2 j hj1 hj2 z hz => ?_⟩
  have := (allIn_eq_true.1 ((allIn_eq_true.1 h7) i hi1 hi2)) j hj1 hj2
  rw [List.all_eq_true] at this
  simpa using this z hz

theorem gs_zero : gs D 0 = a D := by
  rw [gs, slpG_eq, (nest_parts hF).1]
  simp [wordG, genG]

theorem gs_one : gs D 1 = b D := by
  rw [gs, slpG_eq, (nest_parts hF).2.1]
  simp [wordG, genG]

theorem gs_mem_prev : ∀ i, 1 ≤ i → i < D.base.size → ∀ j, D.starts[i]! ≤ j →
    j < D.starts[i + 1]! → gs D j ∈ lvl D (i - 1) := by
  intro i hi1 hi j hj1 hj2
  obtain ⟨-, -, -, -, -, -, hw⟩ := nest_parts hF
  have hsts := hF.starts_size
  rw [gs, slpG_eq]
  unfold wordG
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hz1, hz2⟩ := hw i hi1 (by omega) j hj1 hj2 z hz
  have hst : D.starts[i]! ≤ j := hj1
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  have hm : gs D (z.natAbs - 3) ∈ lvl D (i - 1) := by
    refine gs_mem_lvlGroup (gs D) (by omega) ?_
    rw [show i - 1 + 1 = i by omega]; omega
  split_ifs
  · exact hm
  · exact Subgroup.inv_mem _ hm

theorem chain_facts' :
    (∀ i < D.base.size, TreeFacts D.n (T D)[i]! (levelLv D.starts i) (pairG (gs D)) D.base[i]!) ∧
      (∀ i < D.base.size, ∀ g ∈ lvl D i, idx D.n g D.base[i]! = D.base[i]! ↔ g ∈ lvl D (i + 1)) ∧
      ∀ i ≤ D.base.size, Nat.card (lvl D i) =
        ∏ l ∈ Finset.Ico i D.base.size, (T D)[l]!.pts.size :=
  levelChain_facts (rep_letters hF) (eq_one_of_fix_Q hF.toBaseFacts) (gs_mem_prev hF) hF.chain

theorem lvl_zero : lvl D 0 = ⊤ := by
  rw [eq_top_iff, ← closure_ab D, Subgroup.closure_le]
  obtain ⟨-, -, -, h0, h1, -⟩ := nest_parts hF
  rintro _ (rfl | rfl)
  · rw [← gs_zero hF]; exact gs_mem_lvlGroup (gs D) (by rw [h0]) (by rw [zero_add, h1]; norm_num)
  · rw [← gs_one hF]
    exact gs_mem_lvlGroup (gs D) (by rw [h0]; norm_num) (by rw [zero_add, h1]; norm_num)

theorem n_pos : 0 < D.n := by
  have := hF.vf.size_pos
  rw [hF.keys_size] at this
  exact this

noncomputable abbrev root : Fin D.n := ⟨0, n_pos hF⟩

theorem lvl_one_iff (g : J D) : idx D.n g 0 = 0 ↔ g ∈ lvl D 1 := by
  have := (chain_facts' hF).2.1 0 (by have := hF.base_two; omega) g (by rw [lvl_zero hF]; trivial)
  rwa [hF.base0] at this

theorem stabilizer_root : MulAction.stabilizer (J D) (root hF) = lvl D 1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← lvl_one_iff hF, idx_of_lt g (n_pos hF)]
  constructor
  · intro h; rw [h]
  · intro h; exact Fin.ext h

theorem card_stabilizer_root :
    Nat.card (MulAction.stabilizer (J D) (root hF)) =
      ∏ l ∈ Finset.Ico 1 D.base.size, (T D)[l]!.pts.size := by
  rw [stabilizer_root hF]
  exact (chain_facts' hF).2.2 1 (by have := hF.base_two; omega)

theorem card_J : Nat.card (J D) = ∏ l ∈ Finset.Ico 0 D.base.size, (T D)[l]!.pts.size := by
  rw [← (chain_facts' hF).2.2 0 (Nat.zero_le _), lvl_zero hF, Subgroup.card_top]

theorem lvl_one_fix {g : J D} (hg : g ∈ lvl D 1) : g • root hF = root hF := by
  rw [← MulAction.mem_stabilizer_iff, stabilizer_root hF]; exact hg

theorem treeFacts_zero :
    TreeFacts D.n (T D)[0]! (levelLv D.starts 0) (pairG (gs D)) 0 := by
  have := (chain_facts' hF).1 0 (by have := hF.base_two; omega)
  rwa [hF.base0] at this

theorem isPretransitive : MulAction.IsPretransitive (J D) (Fin D.n) := by
  have hT := treeFacts_zero hF
  have hcard := hT.card_orbit
  rw [hF.T0] at hcard
  set Orb := MulAction.orbit (lettersGroup (levelLv D.starts 0) (pairG (gs D)))
    (⟨0, hT.r_lt⟩ : Fin D.n) with hOrb
  have huniv : Orb = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
  have hreach : ∀ p : Fin D.n, ∃ g : J D, g • root hF = p := by
    intro p
    have hp : p ∈ Orb := by rw [huniv]; trivial
    obtain ⟨⟨g, _⟩, hg⟩ := hp
    exact ⟨g, hg⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, hg⟩ := hreach p
  obtain ⟨h, hh⟩ := hreach q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

end Facts

end CFSG.Sporadic.F5
