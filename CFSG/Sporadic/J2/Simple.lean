module

public import CFSG.Sporadic.J2.Setup
public import CFSG.Sporadic.J1.PrimSpec
public import CFSG.Sporadic.Th.OrbitSpec

public section

namespace CFSG.Sporadic.J2

open CFSG.Blueprint Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.J1 (toV toM toV_mvL toM_mulL toM_idL wfV_iff wfM_iff toV_inj toM_colMat_apply
  eq_one_of_fix_cols isPreprimitive_of_primOK)
open CFSG.Sporadic.J1.Native (Orb orbOK orbCheckAt eqRel vecSep genTables colMat gaussInv wfM
  wfV mvL mulL idL primOK primData)

@[expose] noncomputable def orb : Orb := Native.orbitData ()

noncomputable abbrev letters : Array Table := Native.chainLetters orb

noncomputable abbrev trees : Array Tree := chainTrees 315 letters Native.chainBase

theorem actionChecks_parts :
    orbOK 5 14 eqRel Native.mA Native.mB Native.root orb = true ∧ orb.pts.size = 315 ∧
    vecSep orb.pts = true ∧
    invOK 315 orb.alpha (invT 315 orb.alpha) = true ∧
    invOK 315 orb.beta (invT 315 orb.beta) = true ∧
    chainOK 315 letters Native.chainBase Native.chainQ Native.chainQb trees 3 = true ∧
    orbitSizes trees = [315, 160, 12] ∧
    wfM 14 (Native.qMat orb) = true ∧ wfM 14 (gaussInv 5 14 (Native.qMat orb)) = true ∧
    mulL 5 14 (gaussInv 5 14 (Native.qMat orb)) (Native.qMat orb) = idL 14 ∧
    ap orb.alpha 0 ≠ 0 ∧ ap orb.beta 0 ≠ 0 ∧ ap orb.alpha (ap orb.beta 0) ≠ 0 ∧
    primOK 315 letters (levelLetters letters Native.chainBase 1) trees[0]!
      (primData 315 letters (levelLetters letters Native.chainBase 1) trees[0]!) = true := by
  have h := certificate_parts.2
  unfold Native.actionChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ :=
    h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem orb_size : orb.pts.size = 315 := actionChecks_parts.2.1

theorem orb_at {i : ℕ} (hi : i < 315) :
    wfV 5 14 orb.pts[i]! = true ∧ ap orb.alpha i < 315 ∧ ap orb.beta i < 315 ∧
    eqRel (mvL 5 Native.mA orb.pts[i]!) orb.pts[ap orb.alpha i]! = true ∧
    eqRel (mvL 5 Native.mB orb.pts[i]!) orb.pts[ap orb.beta i]! = true ∧
    (i = 0 ∨ (orb.par[i]! < i ∧ ((orb.lab[i]! = 1 ∧ ap orb.alpha orb.par[i]! = i) ∨
      (orb.lab[i]! = 2 ∧ ap orb.beta orb.par[i]! = i)))) := by
  have h := actionChecks_parts.1
  unfold orbOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hc := (allIn_eq_true.1 h.2) i (Nat.zero_le _) (by rw [orb_size]; exact hi)
  unfold orbCheckAt at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true, orb_size] at hc
  obtain ⟨⟨⟨⟨⟨hv, ha⟩, hb⟩, hra⟩, hrb⟩, ht⟩ := hc
  exact ⟨hv, ha, hb, hra, hrb, ht⟩

noncomputable abbrev vec (i : ℕ) : Fin 14 → ZMod 5 := toV 5 14 orb.pts[i]!

theorem smul_vec_of_eqRel {g : J} {X : List (List ℕ)} (hX : wfM 14 X = true)
    (hg : mat g = toM 5 14 X) {i j : ℕ} (hi : wfV 5 14 orb.pts[i]! = true)
    (h : eqRel (mvL 5 X orb.pts[i]!) orb.pts[j]! = true) : g • vec i = vec j := by
  unfold eqRel at h
  rw [beq_iff_eq] at h
  rw [smul_def, hg, ← toV_mvL hX (wfV_iff.1 hi).1, h]

theorem a_smul_vec
    {i : ℕ} (hi : i < 315) : a • vec i = vec (ap orb.alpha i) :=
  smul_vec_of_eqRel matrix_parts.1 mat_a (orb_at hi).1 (orb_at hi).2.2.2.1

theorem b_smul_vec
    {i : ℕ} (hi : i < 315) : b • vec i = vec (ap orb.beta i) :=
  smul_vec_of_eqRel matrix_parts.2.1 mat_b (orb_at hi).1 (orb_at hi).2.2.2.2.1

theorem vec_inj : ∀ i < 315, ∀ j < 315, vec i = vec j → i = j := by
  have hsep := actionChecks_parts.2.2.1
  unfold vecSep at hsep
  have key : ∀ i j, i < j → j < 315 → vec i = vec j → False := by
    intro i j hij hj he
    have hc := (allIn_eq_true.1 ((allIn_eq_true.1 hsep) i (Nat.zero_le _)
      (by rw [orb_size]; omega))) j (by omega) (by rw [orb_size]; exact hj)
    rw [bne_iff_ne] at hc
    exact hc (toV_inj (orb_at (by omega)).1 (orb_at hj).1 he)
  intro i hi j hj he
  rcases lt_trichotomy i j with h | h | h
  · exact (key i j h hj he).elim
  · exact h
  · exact (key j i h hi he.symm).elim

theorem orbit_hyps :
    (∀ i < 315, ap orb.alpha i < 315 ∧ a • vec i = vec (ap orb.alpha i)) ∧
    (∀ i < 315, ap orb.beta i < 315 ∧ b • vec i = vec (ap orb.beta i)) ∧
    (∀ i < 315, 0 < i → orb.par[i]! < i ∧
      ((orb.lab[i]! = 1 ∧ ap orb.alpha orb.par[i]! = i) ∨
        (orb.lab[i]! = 2 ∧ ap orb.beta orb.par[i]! = i))) :=
  ⟨fun i hi => ⟨(orb_at hi).2.1, a_smul_vec hi⟩, fun i hi => ⟨(orb_at hi).2.2.1, b_smul_vec hi⟩,
    fun i hi hpos => ((orb_at hi).2.2.2.2.2).resolve_left (by omega)⟩

@[expose] noncomputable def ptEquiv :
    Fin 315 ≃ MulAction.orbit J (vec 0) :=
  orbitEquiv closure_ab (by norm_num) vec vec_inj orbit_hyps.1 orbit_hyps.2.1
    (fun i => orb.par[i]!) (fun i => orb.lab[i]!) orbit_hyps.2.2

theorem ptEquiv_apply
    (i : Fin 315) : (ptEquiv i : Fin 14 → ZMod 5) = vec i.val := rfl

noncomputable instance idxInst :
    MulAction J (Fin 315) := ptEquiv.mulAction J

theorem idx_smul_def
    (g : J) (i : Fin 315) : g • i = ptEquiv.symm (g • ptEquiv i) := rfl

theorem vec_smul
    (g : J) (i : Fin 315) : vec (g • i).val = g • vec i.val := by
  have := congrArg Subtype.val (Equiv.apply_symm_apply ptEquiv (g • ptEquiv i))
  rw [← idx_smul_def] at this
  rw [← ptEquiv_apply, this]
  rfl

theorem smul_eq_iff
    (g : J) (i j : Fin 315) : g • i = j ↔ g • vec i.val = vec j.val := by
  constructor
  · rintro rfl; exact (vec_smul g i).symm
  · intro h
    apply Fin.ext
    apply vec_inj _ (g • i).isLt _ j.isLt
    rw [vec_smul, h]

theorem idx_eq_iff {g : J} {i j : ℕ} (hi : i < 315) (hj : j < 315) :
    idx 315 g i = j ↔ g • vec i = vec j := by
  rw [idx_of_lt g hi]
  constructor
  · intro h
    exact (smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).1 (Fin.ext h)
  · intro h
    exact congrArg Fin.val ((smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).2 h)

theorem rep_alpha : Rep 315 orb.alpha a := fun _ hi =>
  ((idx_eq_iff hi (orb_at hi).2.1).2 (a_smul_vec hi)).symm

theorem rep_beta : Rep 315 orb.beta b := fun _ hi =>
  ((idx_eq_iff hi (orb_at hi).2.2.1).2 (b_smul_vec hi)).symm

theorem chainQ_size : Native.chainQ.size = 14 := rfl

theorem qVecs_getD {t : ℕ} (ht : t < 14) :
    (Native.qVecs orb).getD t [] = orb.pts[Native.chainQ[t]!]! := by
  have hl : t < (Native.qVecs orb).length := by simp [Native.qVecs, chainQ_size, ht]
  rw [List.getD_eq_getElem _ _ hl]
  simp only [Native.qVecs, List.getElem_map, Array.getElem_toList]
  rw [getElem!_pos Native.chainQ t (by rw [chainQ_size]; exact ht)]

theorem chainQ_lt {t : ℕ} (ht : t < 14) : Native.chainQ[t]! < 315 := by
  interval_cases t <;> decide

theorem sep (g : J) (hg : ∀ t < Native.chainQ.size,
    idx 315 g Native.chainQ[t]! = Native.chainQ[t]!) : g = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfix : ∀ t < 14, mat g *ᵥ vec Native.chainQ[t]! = vec Native.chainQ[t]! := by
    intro t ht
    exact (idx_eq_iff (chainQ_lt ht) (chainQ_lt ht)).1 (hg t (by rw [chainQ_size]; exact ht))
  obtain ⟨-, -, -, -, -, -, -, hP, hPi, hmul, -⟩ := actionChecks_parts
  have hQP : toM 5 14 (gaussInv 5 14 (Native.qMat orb)) * toM 5 14 (Native.qMat orb) = 1 := by
    rw [← toM_mulL hPi hP, hmul, toM_idL]
  have hcol : ∀ j : Fin 14, mat g *ᵥ (fun i => toM 5 14 (Native.qMat orb) i j) =
      fun i => toM 5 14 (Native.qMat orb) i j := by
    intro j
    have hcolj : (fun i => toM 5 14 (Native.qMat orb) i j) = vec Native.chainQ[j.val]! := by
      funext i
      rw [Native.qMat, toM_colMat_apply _ i j (by simp [Native.qVecs, chainQ_size]),
        qVecs_getD j.isLt]
    rw [hcolj]
    exact hfix j.val j.isLt
  apply mat_injective
  rw [eq_one_of_fix_cols (mat g) _ _ hQP hcol, mat_one]

@[expose] noncomputable def genG (z : ℤ) : J :=
  if z = 1 then a else if z = -1 then a⁻¹ else if z = 2 then b else b⁻¹

theorem rep_gen (z : ℤ) : Rep 315 (genTables orb z) (genG z) := by
  have hsz : orb.pts.size = 315 := orb_size
  unfold genTables genG
  rw [hsz]
  by_cases h1 : z = 1
  · simp only [h1, ite_true]; exact rep_alpha
  · by_cases h2 : z = -1
    · simp only [h2, show (-1 : ℤ) ≠ 1 by decide, ite_false, ite_true]
      exact Rep.inv_of_invOK rep_alpha actionChecks_parts.2.2.2.1
    · by_cases h3 : z = 2
      · simp only [h3, show (2 : ℤ) ≠ 1 by decide, show (2 : ℤ) ≠ -1 by decide, ite_false,
          ite_true]
        exact rep_beta
      · simp only [h1, h2, h3, ite_false]
        exact Rep.inv_of_invOK rep_beta actionChecks_parts.2.2.2.2.1

@[expose] noncomputable def gs (j : ℕ) : J := wordG genG Native.chainWords[j]!

theorem chainWords_size : Native.chainWords.size = 8 := rfl

theorem letters_size : letters.size = 2 * Native.chainWords.size := by
  unfold letters Native.chainLetters buildLetters; simp

theorem letters_even {j : ℕ} (hj : j < Native.chainWords.size) :
    letters[2 * j]! = wordT 315 (genTables orb) Native.chainWords[j]! := by
  unfold letters Native.chainLetters buildLetters
  rw [getElem!_pos _ (2 * j) (by simp; omega), Array.getElem_ofFn]
  simp only
  rw [ite_eq_left (by omega)]
  congr 2
  omega

theorem rep_letters :
    ∀ j < letters.size / 2, Rep 315 letters[2 * j]! (gs j) := by
  intro j hj
  rw [letters_size] at hj
  have hj' : j < Native.chainWords.size := by omega
  rw [letters_even hj']
  exact Rep.wordT (by norm_num) _ fun l _ => rep_gen l

noncomputable abbrev lvl (i : ℕ) : Subgroup J := levelGroup letters Native.chainBase (pairG gs) i

theorem chain_facts' :
    (∀ i < Native.chainBase.size, TreeFacts 315 trees[i]!
      (levelLetters letters Native.chainBase i) (pairG gs) Native.chainBase[i]!) ∧
      (∀ i < Native.chainBase.size, ∀ g ∈ lvl i,
        idx 315 g Native.chainBase[i]! = Native.chainBase[i]! ↔ g ∈ lvl (i + 1)) ∧
      ∀ i ≤ Native.chainBase.size, Nat.card (lvl i) =
        ∏ l ∈ Finset.Ico i Native.chainBase.size, trees[l]!.pts.size :=
  chain_facts rep_letters sep actionChecks_parts.2.2.2.2.2.1

theorem chainBase_size : Native.chainBase.size = 3 := rfl

theorem tree_size_of
    {l v : ℕ} (hv : [315, 160, 12][l]? = some v) : trees[l]!.pts.size = v := by
  have h := actionChecks_parts.2.2.2.2.2.2.1
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

theorem card_lvl_one : Nat.card (lvl 1) = 1920 := by
  rw [chain_facts'.2.2 1 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 1 3, trees[l]!.pts.size = [315, 160, 12].getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem card_lvl_zero : Nat.card (lvl 0) = 604800 := by
  rw [chain_facts'.2.2 0 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 0 3, trees[l]!.pts.size = [315, 160, 12].getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem chainWords_zero : Native.chainWords[0]! = [1] := by decide

theorem chainWords_one : Native.chainWords[1]! = [2] := by decide

theorem chainBase_zero : Native.chainBase[0]! = 0 := by decide

theorem gs_zero : gs 0 = a := by
  rw [gs, chainWords_zero]; simp [wordG, genG]

theorem gs_one : gs 1 = b := by
  rw [gs, chainWords_one]; simp [wordG, genG]

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

noncomputable abbrev root0 : Fin 315 := ⟨0, by norm_num⟩

theorem lvl_one_iff (g : J) : idx 315 g 0 = 0 ↔ g ∈ lvl 1 := by
  have := chain_facts'.2.1 0 (by rw [chainBase_size]; norm_num) g (mem_lvl_zero g)
  rwa [chainBase_zero] at this

theorem stabilizer_root : MulAction.stabilizer J root0 = lvl 1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← lvl_one_iff, idx_of_lt g (by norm_num : 0 < 315)]
  constructor
  · intro h; rw [h]
  · intro h; exact Fin.ext h

theorem card_stabilizer_root :
    Nat.card (MulAction.stabilizer J root0) = 1920 := by
  rw [stabilizer_root]; exact card_lvl_one

theorem treeFacts_zero :
    TreeFacts 315 trees[0]! (levelLetters letters Native.chainBase 0)
    (pairG gs) 0 := by
  have := chain_facts'.1 0 (by rw [chainBase_size]; norm_num)
  rwa [chainBase_zero] at this

instance isPretransitive :
    MulAction.IsPretransitive J (Fin 315) := by
  have hT := treeFacts_zero
  have hcard := hT.card_orbit
  rw [tree_size_of (l := 0) rfl] at hcard
  set O := MulAction.orbit (lettersGroup (levelLetters letters Native.chainBase 0) (pairG gs))
    (⟨0, hT.r_lt⟩ : Fin 315) with hO
  have huniv : O = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
  have hreach : ∀ p : Fin 315, ∃ g : J, g • root0 = p := by
    intro p
    have hp : p ∈ O := by rw [huniv]; trivial
    obtain ⟨⟨g, _⟩, hg⟩ := hp
    exact ⟨g, hg⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, hg⟩ := hreach p
  obtain ⟨h, hh⟩ := hreach q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

theorem rep_pairG_all :
    ∀ l < letters.size, Rep 315 letters[l]! (pairG gs l) :=
  rep_pairG rep_letters (by rw [letters_size]; omega)
    (chainOK_parts actionChecks_parts.2.2.2.2.2.1).2.1

theorem walkFacts_zero :
    WalkFacts 315 trees[0]! letters (pairG gs) := by
  intro k hk hk0
  obtain ⟨hpar, hlab⟩ := treeFacts_zero.par k hk hk0
  have hl := levelLetters_lt hlab
  refine ⟨hpar, rep_pairG_all _ hl, ?_⟩
  rw [← pairG_invL]
  exact rep_pairG_all _ (invL_lt (by rw [letters_size]; omega) hl)

theorem isPreprimitive : MulAction.IsPreprimitive J (Fin 315) :=
  isPreprimitive_of_primOK treeFacts_zero walkFacts_zero
    (fun l hl => rep_pairG_all l (levelLetters_lt hl))
    (fun g hg => (lvl_one_iff g).2 hg) actionChecks_parts.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem a_ne_one : a ≠ 1 := by
  intro h
  apply actionChecks_parts.2.2.2.2.2.2.2.2.2.2.1
  rw [rep_alpha 0 (by norm_num), h, idx_one]

theorem b_ne_one : b ≠ 1 := by
  intro h
  apply actionChecks_parts.2.2.2.2.2.2.2.2.2.2.2.1
  rw [rep_beta 0 (by norm_num), h, idx_one]

theorem ab_ne_one : a * b ≠ 1 := by
  intro h
  apply actionChecks_parts.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [rep_beta 0 (by norm_num), rep_alpha _ (idx_lt b (by norm_num)), ← idx_mul, h, idx_one]

theorem orderOf_a : orderOf a = 2 := orderOf_eq_prime a_sq a_ne_one

theorem orderOf_b : orderOf b = 3 := orderOf_eq_prime b_cube b_ne_one

theorem orderOf_ab : orderOf (a * b) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime ab_pow ab_ne_one

instance faithful : FaithfulSMul J (Fin 315) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := sep _ fun t ht => by
    have hQ : Native.chainQ[t]! < 315 := chainQ_lt (by rw [chainQ_size] at ht; exact ht)
    rw [idx_of_lt _ hQ, mul_smul, hgh, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem isSimpleGroup_J : IsSimpleGroup J := by
  have := isPreprimitive
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Fin 315) ?_ a b closure_ab root0
    ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  · rw [orderOf_a, orderOf_b]; norm_num
  · rw [orderOf_ab, card_stabilizer_root]; norm_num

theorem card_J : Nat.card J = 604800 := by
  rw [← card_lvl_zero, lvl_zero, Subgroup.card_top]

end CFSG.Sporadic.J2
