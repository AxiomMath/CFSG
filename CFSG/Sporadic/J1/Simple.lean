module

public import CFSG.Sporadic.J1.Setup
public import CFSG.Sporadic.J1.PrimSpec
public import CFSG.Sporadic.J1.Certificate
public import CFSG.Sporadic.Th.OrbitSpec

public section

namespace CFSG.Sporadic.J1

open CFSG.Blueprint CFSG.ProperTwoGeneratedCore Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Perm CFSG.Perm.Native Native

@[expose] noncomputable def orb : Orb := orbitData ()

noncomputable abbrev letters : Array Table := chainLetters orb

noncomputable abbrev trees : Array Tree := chainTrees 1540 letters chainBase

theorem certificate_parts :
    actionChecks orb 3 = true := j1_certificate

theorem actionChecks_parts :
    orbOK 11 7 (pmRel 11) mA mB root orb = true ∧ orb.pts.size = 1540 ∧
    pmSep 11 7 orb.pts 3 = true ∧
    invOK 1540 orb.alpha (invT 1540 orb.alpha) = true ∧
    invOK 1540 orb.beta (invT 1540 orb.beta) = true ∧
    chainOK 1540 letters chainBase chainQ chainQb trees 3 = true ∧
    orbitSizes trees = [1540, 114] ∧
    wfM 7 (qMat orb) = true ∧ wfM 7 (gaussInv 11 7 (qMat orb)) = true ∧
    mulL 11 7 (gaussInv 11 7 (qMat orb)) (qMat orb) = idL 7 ∧
    ((mvL 11 (gaussInv 11 7 (qMat orb)) ((qVecs orb).getD 7 [])).all fun x => x != 0) = true ∧
    primOK 1540 letters (levelLetters letters chainBase 1) trees[0]!
      (primData 1540 letters (levelLetters letters chainBase 1) trees[0]!) = true := by
  have h := certificate_parts
  unfold actionChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem orb_size : orb.pts.size = 1540 := actionChecks_parts.2.1

theorem orb_at {i : ℕ} (hi : i < 1540) :
    wfV 11 7 orb.pts[i]! = true ∧ ap orb.alpha i < 1540 ∧ ap orb.beta i < 1540 ∧
    pmRel 11 (mvL 11 mA orb.pts[i]!) orb.pts[ap orb.alpha i]! = true ∧
    pmRel 11 (mvL 11 mB orb.pts[i]!) orb.pts[ap orb.beta i]! = true ∧
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

noncomputable abbrev vec (i : ℕ) : Fin 7 → ZMod 11 := toV 11 7 orb.pts[i]!

noncomputable abbrev pt (i : ℕ) : Cong := ⟨vecMulVec (vec i) (vec i)⟩

theorem mvL_lt {p : ℕ} (hp : 0 < p) (X : List (List ℕ)) (v : List ℕ) : ∀ x ∈ mvL p X v, x < p := by
  intro x hx
  simp only [mvL, List.mem_map] at hx
  obtain ⟨_, _, rfl⟩ := hx
  exact Nat.mod_lt _ hp

theorem mvL_length (p : ℕ) (X : List (List ℕ)) (v : List ℕ) : (mvL p X v).length = X.length := by
  simp [mvL]

theorem smul_pt_of_pmRel {g : J} {X : List (List ℕ)} (hX : wfM 7 X = true)
    (hg : mat g = toM 11 7 X) {i j : ℕ} (hi : wfV 11 7 orb.pts[i]! = true)
    (hj : wfV 11 7 orb.pts[j]! = true) (h : pmRel 11 (mvL 11 X orb.pts[i]!) orb.pts[j]! = true) :
    g • pt i = pt j := by
  rw [smul_vecMulVec]
  have hv : mat g *ᵥ vec i = toV 11 7 (mvL 11 X orb.pts[i]!) := by
    rw [hg, toV_mvL hX (wfV_iff.1 hi).1]
  rw [hv]
  unfold pmRel at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · rw [h]
  · rw [h, toV_negL (wfV_iff.1 hj).2]
    ext1
    ext x y
    simp [vecMulVec_apply]

theorem a_smul_pt
    {i : ℕ} (hi : i < 1540) : a • pt i = pt (ap orb.alpha i) :=
  smul_pt_of_pmRel wfM_mA (by rw [mat_a, toM_mA]) (orb_at hi).1 (orb_at (orb_at hi).2.1).1
    (orb_at hi).2.2.2.1

theorem b_smul_pt
    {i : ℕ} (hi : i < 1540) : b • pt i = pt (ap orb.beta i) :=
  smul_pt_of_pmRel wfM_mB (by rw [mat_b, toM_mB]) (orb_at hi).1 (orb_at (orb_at hi).2.2.1).1
    (orb_at hi).2.2.2.2.1

theorem minor_ne_of_minorNZ {u w : List ℕ} (h : minorNZ 11 7 u w = true) :
    ∃ x y : Fin 7, toV 11 7 u x * toV 11 7 w y ≠ toV 11 7 u y * toV 11 7 w x := by
  unfold minorNZ at h
  simp only [List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ?_⟩
  simp only [toV]
  rw [← Nat.cast_mul, ← Nat.cast_mul]
  intro e
  exact hxy ((ZMod.natCast_eq_natCast_iff' _ _ 11).1 e)

theorem pt_inj : ∀ i < 1540, ∀ j < 1540, pt i = pt j → i = j := by
  have hsep := parAll_eq_true actionChecks_parts.2.2.1
  have key : ∀ i j, i < j → j < 1540 → pt i = pt j → False := by
    intro i j hij hj he
    have hc := (allIn_eq_true.1 (hsep i (by rw [orb_size]; omega))) j (by omega)
      (by rw [orb_size]; exact hj)
    obtain ⟨x, y, hxy⟩ := minor_ne_of_minorNZ hc
    have hm : vecMulVec (vec i) (vec i) = vecMulVec (vec j) (vec j) := congrArg Cong.val he
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact hxy (minor_eq_of_vecMulVec_eq hm x y)
  intro i hi j hj he
  rcases lt_trichotomy i j with h | h | h
  · exact (key i j h hj he).elim
  · exact h
  · exact (key j i h hi he.symm).elim

theorem orbit_hyps :
    (∀ i < 1540, ap orb.alpha i < 1540 ∧ a • pt i = pt (ap orb.alpha i)) ∧
    (∀ i < 1540, ap orb.beta i < 1540 ∧ b • pt i = pt (ap orb.beta i)) ∧
    (∀ i < 1540, 0 < i → orb.par[i]! < i ∧
      ((orb.lab[i]! = 1 ∧ ap orb.alpha orb.par[i]! = i) ∨
        (orb.lab[i]! = 2 ∧ ap orb.beta orb.par[i]! = i))) :=
  ⟨fun i hi => ⟨(orb_at hi).2.1, a_smul_pt hi⟩, fun i hi => ⟨(orb_at hi).2.2.1, b_smul_pt hi⟩,
    fun i hi hpos => ((orb_at hi).2.2.2.2.2).resolve_left (by omega)⟩

@[expose] noncomputable def ptEquiv :
    Fin 1540 ≃ MulAction.orbit J (pt 0) :=
  orbitEquiv closure_ab (by norm_num) pt pt_inj orbit_hyps.1 orbit_hyps.2.1 (fun i => orb.par[i]!)
    (fun i => orb.lab[i]!) orbit_hyps.2.2

theorem ptEquiv_apply
    (i : Fin 1540) : (ptEquiv i : Cong) = pt i.val := rfl

noncomputable instance idxInst :
    MulAction J (Fin 1540) := ptEquiv.mulAction J

theorem smul_def
    (g : J) (i : Fin 1540) : g • i = ptEquiv.symm (g • ptEquiv i) := rfl

theorem pt_smul
    (g : J) (i : Fin 1540) : pt (g • i).val = g • pt i.val := by
  have := congrArg Subtype.val (Equiv.apply_symm_apply ptEquiv (g • ptEquiv i))
  rw [← smul_def] at this
  rw [← ptEquiv_apply, this]
  rfl

theorem smul_eq_iff
    (g : J) (i j : Fin 1540) : g • i = j ↔ g • pt i.val = pt j.val := by
  constructor
  · rintro rfl; exact (pt_smul g i).symm
  · intro h
    apply Fin.ext
    apply pt_inj _ (g • i).isLt _ j.isLt
    rw [pt_smul, h]

theorem idx_eq_iff
    {g : J} {i j : ℕ} (hi : i < 1540) (hj : j < 1540) :
    idx 1540 g i = j ↔ g • pt i = pt j := by
  rw [idx_of_lt g hi]
  constructor
  · intro h
    exact (smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).1 (Fin.ext h)
  · intro h
    exact congrArg Fin.val ((smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).2 h)

theorem rep_alpha : Rep 1540 orb.alpha a := fun _ hi =>
  ((idx_eq_iff hi (orb_at hi).2.1).2 (a_smul_pt hi)).symm

theorem rep_beta : Rep 1540 orb.beta b := fun _ hi =>
  ((idx_eq_iff hi (orb_at hi).2.2.1).2 (b_smul_pt hi)).symm

theorem chainQ_size : chainQ.size = 8 := rfl

theorem qVecs_getD {t : ℕ} (ht : t < 8) : (qVecs orb).getD t [] = orb.pts[chainQ[t]!]! := by
  have hl : t < (qVecs orb).length := by simp [qVecs, chainQ_size, ht]
  rw [List.getD_eq_getElem _ _ hl]
  simp only [qVecs, List.getElem_map, Array.getElem_toList]
  rw [getElem!_pos chainQ t (by rw [chainQ_size]; exact ht)]

theorem getD_take_of_lt {α : Type*} (l : List α) (d : α) {n i : ℕ} (h : i < n) :
    (l.take n).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem chainQ_lt {t : ℕ} (ht : t < 8) : chainQ[t]! < 1540 := by
  interval_cases t <;> decide

theorem sep
    (g : J) (hg : ∀ t < chainQ.size, idx 1540 g chainQ[t]! = chainQ[t]!) : g = 1 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have heig : ∀ t < 8, ∃ c : ZMod 11, mat g *ᵥ vec chainQ[t]! = c • vec chainQ[t]! := by
    intro t ht
    have h := (idx_eq_iff (chainQ_lt ht) (chainQ_lt ht)).1 (hg t (by rw [chainQ_size]; exact ht))
    rw [smul_vecMulVec] at h
    have h' : vecMulVec (mat g *ᵥ vec chainQ[t]!) (mat g *ᵥ vec chainQ[t]!) =
        vecMulVec (vec chainQ[t]!) (vec chainQ[t]!) := congrArg Cong.val h
    exact exists_smul_of_vecMulVec_eq h'
  obtain ⟨-, -, -, -, -, -, -, hP, hPi, hmul, hall, -⟩ := actionChecks_parts
  have hQP : toM 11 7 (gaussInv 11 7 (qMat orb)) * toM 11 7 (qMat orb) = 1 := by
    rw [← toM_mulL hPi hP, hmul, toM_idL]
  have hwf7 := (orb_at (chainQ_lt (t := 7) (by norm_num))).1
  have hc : ∀ i, (toM 11 7 (gaussInv 11 7 (qMat orb)) *ᵥ vec chainQ[7]!) i ≠ 0 := by
    intro i
    rw [vec, ← qVecs_getD (by norm_num), ← toV_mvL hPi (by
      rw [qVecs_getD (by norm_num)]; exact (wfV_iff.1 hwf7).1)]
    exact toV_ne_zero_of_all (by rw [mvL_length, (wfM_iff.1 hPi).1]) (mvL_lt (by norm_num) _ _)
      hall i
  have hcol : ∀ j : Fin 7, ∃ c : ZMod 11, mat g *ᵥ (fun i => toM 11 7 (qMat orb) i j) =
      c • fun i => toM 11 7 (qMat orb) i j := by
    intro j
    have hcolj : (fun i => toM 11 7 (qMat orb) i j) = vec chainQ[j.val]! := by
      funext i
      rw [qMat, toM_colMat_apply _ i j (by simp [qVecs, chainQ_size]),
        getD_take_of_lt _ _ j.isLt, qVecs_getD (by omega)]
    rw [hcolj]
    exact heig j.val (by omega)
  obtain ⟨μ, hμ⟩ := eq_smul_one_of_eigen (mat g) _ _ hQP (vec chainQ[7]!) hc hcol
    (heig 7 (by norm_num))
  exact eq_one_of_smul_one hμ

@[expose] noncomputable def genG (z : ℤ) : J :=
  if z = 1 then a else if z = -1 then a⁻¹ else if z = 2 then b else b⁻¹

theorem rep_gen (z : ℤ) : Rep 1540 (genTables orb z) (genG z) := by
  have hsz : orb.pts.size = 1540 := orb_size
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

@[expose] noncomputable def gs (j : ℕ) : J := wordG genG chainWords[j]!

theorem chainWords_size : chainWords.size = 5 := rfl

theorem letters_size : letters.size = 2 * chainWords.size := by
  unfold letters chainLetters buildLetters; simp

theorem letters_even {j : ℕ} (hj : j < chainWords.size) :
    letters[2 * j]! = wordT 1540 (genTables orb) chainWords[j]! := by
  unfold letters chainLetters buildLetters
  rw [getElem!_pos _ (2 * j) (by simp; omega), Array.getElem_ofFn]
  simp only
  rw [ite_eq_left (by omega)]
  congr 2
  omega

theorem rep_letters :
    ∀ j < letters.size / 2, Rep 1540 letters[2 * j]! (gs j) := by
  intro j hj
  rw [letters_size] at hj
  have hj' : j < chainWords.size := by omega
  rw [letters_even hj']
  exact Rep.wordT (by norm_num) _ fun l _ => rep_gen l

noncomputable abbrev lvl (i : ℕ) : Subgroup J := levelGroup letters chainBase (pairG gs) i

theorem chain_facts' :
    (∀ i < chainBase.size, TreeFacts 1540 trees[i]! (levelLetters letters chainBase i)
      (pairG gs) chainBase[i]!) ∧
      (∀ i < chainBase.size, ∀ g ∈ lvl i, idx 1540 g chainBase[i]! = chainBase[i]! ↔
        g ∈ lvl (i + 1)) ∧
      ∀ i ≤ chainBase.size, Nat.card (lvl i) =
        ∏ l ∈ Finset.Ico i chainBase.size, trees[l]!.pts.size :=
  chain_facts rep_letters sep actionChecks_parts.2.2.2.2.2.1

theorem chainBase_size : chainBase.size = 2 := rfl

theorem tree_size_of
    {l v : ℕ} (hv : [1540, 114][l]? = some v) : trees[l]!.pts.size = v := by
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

theorem card_lvl_one : Nat.card (lvl 1) = 114 := by
  rw [chain_facts'.2.2 1 (by rw [chainBase_size]; norm_num), chainBase_size]
  rw [show Finset.Ico 1 2 = {1} by decide, Finset.prod_singleton, tree_size_of (l := 1) rfl]

theorem card_lvl_zero : Nat.card (lvl 0) = 175560 := by
  rw [chain_facts'.2.2 0 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 0 2, trees[l]!.pts.size = [1540, 114].getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem chainWords_zero : chainWords[0]! = [1] := by decide

theorem chainWords_one : chainWords[1]! = [2] := by decide

theorem chainBase_zero : chainBase[0]! = 0 := by decide

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

noncomputable abbrev root0 : Fin 1540 := ⟨0, by norm_num⟩

theorem lvl_one_iff (g : J) : idx 1540 g 0 = 0 ↔ g ∈ lvl 1 := by
  have := chain_facts'.2.1 0 (by rw [chainBase_size]; norm_num) g (mem_lvl_zero g)
  rwa [chainBase_zero] at this

theorem stabilizer_root : MulAction.stabilizer J root0 = lvl 1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← lvl_one_iff, idx_of_lt g (by norm_num : 0 < 1540)]
  constructor
  · intro h; rw [h]
  · intro h; exact Fin.ext h

theorem card_stabilizer_root :
    Nat.card (MulAction.stabilizer J root0) = 114 := by
  rw [stabilizer_root]; exact card_lvl_one

theorem treeFacts_zero :
    TreeFacts 1540 trees[0]! (levelLetters letters chainBase 0)
    (pairG gs) 0 := by
  have := chain_facts'.1 0 (by rw [chainBase_size]; norm_num)
  rwa [chainBase_zero] at this

instance isPretransitive :
    MulAction.IsPretransitive J (Fin 1540) := by
  have hT := treeFacts_zero
  have hcard := hT.card_orbit
  rw [tree_size_of (l := 0) rfl] at hcard
  set O := MulAction.orbit (lettersGroup (levelLetters letters chainBase 0) (pairG gs))
    (⟨0, hT.r_lt⟩ : Fin 1540) with hO
  have huniv : O = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
  have hreach : ∀ p : Fin 1540, ∃ g : J, g • root0 = p := by
    intro p
    have hp : p ∈ O := by rw [huniv]; trivial
    obtain ⟨⟨g, _⟩, hg⟩ := hp
    exact ⟨g, hg⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, hg⟩ := hreach p
  obtain ⟨h, hh⟩ := hreach q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

theorem rep_pairG_all :
    ∀ l < letters.size, Rep 1540 letters[l]! (pairG gs l) :=
  rep_pairG rep_letters (by rw [letters_size]; omega)
    (chainOK_parts actionChecks_parts.2.2.2.2.2.1).2.1

theorem walkFacts_zero :
    WalkFacts 1540 trees[0]! letters (pairG gs) := by
  intro k hk hk0
  obtain ⟨hpar, hlab⟩ := treeFacts_zero.par k hk hk0
  have hl := levelLetters_lt hlab
  refine ⟨hpar, rep_pairG_all _ hl, ?_⟩
  rw [← pairG_invL]
  exact rep_pairG_all _ (invL_lt (by rw [letters_size]; omega) hl)

theorem isPreprimitive : MulAction.IsPreprimitive J (Fin 1540) :=
  isPreprimitive_of_primOK treeFacts_zero walkFacts_zero
    (fun l hl => rep_pairG_all l (levelLetters_lt hl))
    (fun g hg => (lvl_one_iff g).2 hg) actionChecks_parts.2.2.2.2.2.2.2.2.2.2.2

instance faithful : FaithfulSMul J (Fin 1540) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := sep _ fun t ht => by
    have hQ : chainQ[t]! < 1540 := chainQ_lt (by rw [chainQ_size] at ht; exact ht)
    rw [idx_of_lt _ hQ, mul_smul, hgh, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem isSimpleGroup_J : IsSimpleGroup J := by
  have := isPreprimitive
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Fin 1540) ?_ a b closure_ab root0
    ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  · rw [orderOf_a, orderOf_b]; norm_num
  · rw [orderOf_ab, card_stabilizer_root]; norm_num

theorem card_J : Nat.card J = 175560 := by
  rw [← card_lvl_zero, lvl_zero, Subgroup.card_top]

end CFSG.Sporadic.J1
