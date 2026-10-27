
module

public import CFSG.Sporadic.Fi24.SimpleBase
import all CFSG.Sporadic.Fi24.SimpleBase

public import CFSG.Sporadic.Fi24.Orbit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native CFSG.Sporadic.Fi24.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native

theorem J_eq_closure :
    J = Subgroup.closure {g : GL (Fin 781) (ZMod 3) | g.val = mA ∨ g.val = mB} := by
  have hs : ({gA, gB} : Set (GL (Fin 781) (ZMod 3))) = {g | g.val = mA ∨ g.val = mB} := by
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact Or.inl (Units.ext h)
      · exact Or.inr (Units.ext h)
  change Subgroup.closure ({gA, gB} : Set (GL (Fin 781) (ZMod 3))) = _
  rw [hs]

theorem card_J : Nat.card J = 1255205709190661721292800 := by
  rw [J_eq_closure]
  exact core_facts.card

theorem actionFacts : ActionFacts where
  beta_inv := by
    unfold invOK
    refine allIn_eq_true.2 fun i _ hi => ?_
    rw [beq_iff_eq]
    exact core_facts.beta_inv i hi
  slp_ok := core_facts.slp_ok
  words_size := by decide
  word0 := by decide
  word1 := by decide

@[expose] noncomputable def genG (z : ℤ) : J :=
  if z = 1 then a else if z = -1 then a⁻¹ else if z = 2 then b else b⁻¹

theorem rep_gen (z : ℤ) : Rep 306936 (CFSG.Sporadic.Fi24.Native.genTables orb z) (genG z) := by
  unfold CFSG.Sporadic.Fi24.Native.genTables genG
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

@[expose] noncomputable def gs (j : ℕ) : J := slpG genG CFSG.Sporadic.Fi24.Native.chainWords j

theorem letters_size : letters.size = 2 * CFSG.Sporadic.Fi24.Native.chainWords.size := by
  rw [core_facts.letters_size, actionFacts.words_size]

theorem letters_invOK :
    ∀ j < letters.size / 2, invOK 306936 letters[2 * j]! letters[2 * j + 1]! = true := by
  intro j hj
  rw [core_facts.letters_size] at hj
  unfold invOK
  refine allIn_eq_true.2 fun x _ hx => ?_
  rw [beq_iff_eq]
  exact (core_facts.letters j (by omega) x hx).2

theorem rep_letters :
    ∀ j < letters.size / 2, Rep 306936 letters[2 * j]! (gs j) := by
  intro j hj
  rw [letters_size] at hj
  refine rep_slpLetters (by norm_num) rep_gen actionFacts.slp_ok (fun i hi => ?_) j (by omega)
  exact letters_invOK i (by rw [letters_size]; omega)

theorem rep_pairG_all :
    ∀ l < letters.size, Rep 306936 letters[l]! (pairG gs l) :=
  rep_pairG rep_letters (by rw [letters_size]; omega) letters_invOK

noncomputable abbrev lvl
    (i : ℕ) : Subgroup J := levelGroup letters CFSG.Sporadic.Fi24.Native.chainBase (pairG gs) i

theorem gs_zero : gs 0 = a := by
  rw [gs, slpG_eq, actionFacts.word0]
  simp [wordG, genG]

theorem gs_one : gs 1 = b := by
  rw [gs, slpG_eq, actionFacts.word1]
  simp [wordG, genG]

theorem a_mem_lvl_zero : a ∈ lvl 0 := by
  have hsz : 0 < letters.size := by rw [letters_size, actionFacts.words_size]; decide
  have : pairG gs 0 = a := by simp [pairG, gs_zero]
  rw [← this]
  exact lG_mem (mem_levelLetters_zero.2 hsz)

theorem b_mem_lvl_zero : b ∈ lvl 0 := by
  have hsz : 2 < letters.size := by rw [letters_size, actionFacts.words_size]; decide
  have : pairG gs 2 = b := by simp [pairG, gs_one]
  rw [← this]
  exact lG_mem (mem_levelLetters_zero.2 hsz)

theorem lvl_zero : lvl 0 = ⊤ := by
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact a_mem_lvl_zero
  · exact b_mem_lvl_zero

theorem mem_lvl_zero (g : J) : g ∈ lvl 0 := by rw [lvl_zero]; trivial

theorem orbit_of_chainOrbit {lv : Array ℕ}
    (hlv : ∀ l ∈ lv, l < letters.size) {y c : ℕ} (hy : y < 306936)
    (h : ChainOrbit letters lv y c) :
    Nat.card (MulAction.orbit (lettersGroup lv (pairG gs)) (⟨y, hy⟩ : Fin 306936)) = c := by
  obtain ⟨P, hc, hyP, hPn, hcl, hw⟩ := h
  rw [(orbit_of_set (fun l hl => rep_pairG_all l (hlv l hl)) hy P hyP hPn hcl hw).2, hc]

theorem chain_facts' :
    (∀ i (hi : i < CFSG.Sporadic.Fi24.Native.chainBase.size), Nat.card (MulAction.orbit (lvl i)
      (⟨CFSG.Sporadic.Fi24.Native.chainBase[i]!, chainBase_get_lt hi⟩ : Fin 306936)) = chainSizes[i]!) ∧
      (∀ i < CFSG.Sporadic.Fi24.Native.chainBase.size, ∀ g ∈ lvl i, idx 306936 g CFSG.Sporadic.Fi24.Native.chainBase[i]! = CFSG.Sporadic.Fi24.Native.chainBase[i]! ↔
        g ∈ lvl (i + 1)) ∧
      ∀ i ≤ CFSG.Sporadic.Fi24.Native.chainBase.size, Nat.card (lvl i) =
        ∏ l ∈ Finset.Ico i CFSG.Sporadic.Fi24.Native.chainBase.size, chainSizes[l]! := by
  have horb : ∀ i (hi : i < CFSG.Sporadic.Fi24.Native.chainBase.size), Nat.card (MulAction.orbit (lvl i)
      (⟨CFSG.Sporadic.Fi24.Native.chainBase[i]!, chainBase_get_lt hi⟩ : Fin 306936)) = chainSizes[i]! := fun i hi =>
    orbit_of_chainOrbit (fun _ hl => levelLetters_lt hl) _
      (core_facts.orbits i (by rw [chainBase_size] at hi; exact hi))
  refine ⟨horb, chain_of_orbits rep_pairG_all (fun i hi => chainBase_get_lt hi) _ horb lvl_zero ?_⟩
  rw [card_J, chainBase_size]
  decide

theorem card_lvl_one : Nat.card (lvl 1) = 4089470473293004800 := by
  rw [chain_facts'.2.2 1 (by rw [chainBase_size]; norm_num), chainBase_size]
  rw [show Finset.Ico 1 6 = {1, 2, 3, 4, 5} by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
    tree_size_of (l := 1) rfl, tree_size_of (l := 2) rfl, tree_size_of (l := 3) rfl,
    tree_size_of (l := 4) rfl, tree_size_of (l := 5) rfl]
  norm_num

theorem card_lvl_zero :
    Nat.card (lvl 0) = 1255205709190661721292800 := by
  rw [lvl_zero, Subgroup.card_top, card_J]

theorem sep
    (g : J) (hg : ∀ t < CFSG.Sporadic.Fi24.Native.chainBase.size, idx 306936 g CFSG.Sporadic.Fi24.Native.chainBase[t]! = CFSG.Sporadic.Fi24.Native.chainBase[t]!) :
    g = 1 := by
  have hmem : ∀ i ≤ CFSG.Sporadic.Fi24.Native.chainBase.size, g ∈ lvl i := by
    intro i
    induction i with
    | zero => intro _; exact mem_lvl_zero g
    | succ i ih =>
      intro hi
      exact (chain_facts'.2.1 i (by omega) g (ih (by omega))).1 (hg i (by omega))
  have h6 := chain_facts'.2.2 6 (by rw [chainBase_size])
  rw [chainBase_size, Finset.Ico_self, Finset.prod_empty] at h6
  have := hmem 6 (by rw [chainBase_size])
  rw [Subgroup.eq_bot_of_card_eq _ h6] at this
  exact (Subgroup.mem_bot.1 this)

instance faithful : FaithfulSMul J (Fin 306936) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := sep _ fun t ht => by
    rw [idx_of_lt _ (chainBase_get_lt ht), mul_smul, hgh, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem lvl_one_iff (g : J) : idx 306936 g 0 = 0 ↔ g ∈ lvl 1 := by
  have := chain_facts'.2.1 0 (by rw [chainBase_size]; norm_num) g (mem_lvl_zero g)
  rwa [chainBase_zero] at this

theorem stabilizer_root : MulAction.stabilizer J root = lvl 1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← lvl_one_iff, idx_of_lt g (by norm_num : 0 < 306936)]
  constructor
  · intro h; rw [h]
  · intro h; exact Fin.ext h

theorem card_stabilizer_root :
    Nat.card (MulAction.stabilizer J root) = 4089470473293004800 := by
  rw [stabilizer_root]; exact card_lvl_one

theorem lvl_one_fix {g : J} (hg : g ∈ lvl 1) : g • root = root := by
  rw [← MulAction.mem_stabilizer_iff, stabilizer_root]; exact hg

instance isPretransitive :
    MulAction.IsPretransitive J (Fin 306936) := by
  have hcard := chain_facts'.1 0 (by rw [chainBase_size]; norm_num)
  rw [tree_size_of (l := 0) rfl] at hcard
  set O := MulAction.orbit (lvl 0)
    (⟨CFSG.Sporadic.Fi24.Native.chainBase[0]!, chainBase_get_lt (by rw [chainBase_size]; norm_num)⟩ : Fin 306936) with hO
  have huniv : O = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
  have hreach : ∀ p : Fin 306936, ∃ g : J, g • root = p := by
    intro p
    have hp : p ∈ O := by rw [huniv]; trivial
    obtain ⟨⟨g, _⟩, hg⟩ := hp
    refine ⟨g, ?_⟩
    rw [← hg]
    rfl
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, hg⟩ := hreach p
  obtain ⟨h, hh⟩ := hreach q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

noncomputable abbrev orbOne : Set (Fin 306936) :=
  MulAction.orbit (lvl 1) (⟨305530, by norm_num⟩ : Fin 306936)

noncomputable abbrev orbTwo : Set (Fin 306936) :=
  MulAction.orbit (lvl 1) (⟨CFSG.Sporadic.Fi24.Native.subRoot, by decide⟩ : Fin 306936)

theorem card_orbOne : Nat.card orbOne = 275264 := by
  have := chain_facts'.1 1 (by rw [chainBase_size]; norm_num)
  rwa [tree_size_of (l := 1) rfl] at this

theorem card_orbTwo : Nat.card orbTwo = 31671 :=
  orbit_of_chainOrbit (fun _ hl => levelLetters_lt hl) _ core_facts.sub_orbit

theorem inOrbOne_iff (p : Fin 306936) : InOrbOne p ↔ p ∈ orbOne := by
  have hrep : ∀ l ∈ lv1, Rep 306936 letters[l]! (pairG gs l) :=
    fun l hl => rep_pairG_all l (levelLetters_lt hl)
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨e, hm⟩ := foldr_rep hrep w hw p.val p.isLt
    refine ⟨⟨((w.map (pairG gs)).prod)⁻¹, (lvl 1).inv_mem hm⟩, ?_⟩
    change ((w.map (pairG gs)).prod)⁻¹ • (⟨305530, by norm_num⟩ : Fin 306936) = p
    rw [inv_smul_eq_iff]
    apply Fin.ext
    rw [← idx_of_lt _ p.isLt, ← e, he]
  · intro hp
    obtain ⟨P, -, hyP, hPn, hcl, hw⟩ := core_facts.orbits 1 (by norm_num)
    rw [chainBase_one] at hyP hw
    have hset := (orbit_of_set hrep (by norm_num) P hyP hPn hcl hw).1
    have hp' : p ∈ ({q | q.val ∈ P} : Set (Fin 306936)) := by
      rw [← hset]
      exact hp
    exact hw p.val hp'

theorem orbit_smul_mem
    {H : Subgroup J} {x p : Fin 306936} (h : J) (hh : h ∈ H)
    (hp : p ∈ MulAction.orbit H x) : h • p ∈ MulAction.orbit H x := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := hp
  refine ⟨⟨h * k, H.mul_mem hh hk⟩, ?_⟩
  change (h * k) • x = h • (k • x)
  exact mul_smul h k x

theorem not_root_of_orbit {x p : Fin 306936} (hx : x ≠ root)
    (hp : p ∈ MulAction.orbit (lvl 1) x) : p ≠ root := by
  rintro rfl
  obtain ⟨⟨k, hk⟩, hkp⟩ := hp
  apply hx
  have : (k⁻¹ : J) • root = x := by
    rw [← hkp]
    exact inv_smul_smul k _
  rw [← this, lvl_one_fix ((lvl 1).inv_mem hk)]

theorem orbit_one_ne_zero (p : Fin 306936)
    (hp : p ∈ MulAction.orbit (lvl 1) (⟨305530, by norm_num⟩ : Fin 306936)) :
    p.val ≠ 0 := fun h0 => not_root_of_orbit (by decide) hp (Fin.ext h0)

theorem subLab_eq_one {p : Fin 306936} :
    subLab p = 1 ↔ p ∈ MulAction.orbit (lvl 1) (⟨305530, by norm_num⟩ : Fin 306936) := by
  change _ ↔ p ∈ orbOne
  rw [← inOrbOne_iff]
  unfold subLab
  constructor
  · intro h
    split_ifs at h with h0 h1
    · exact absurd h (by decide)
    · exact h1
    · exact absurd h (by decide)
  · intro h
    have h0 : p.val ≠ 0 := orbit_one_ne_zero p ((inOrbOne_iff p).1 h)
    rw [ite_eq_right h0, ite_eq_left h]

theorem subLab_eq_two {p : Fin 306936} :
    subLab p = 2 ↔
      p ≠ root ∧ p ∉ MulAction.orbit (lvl 1) (⟨305530, by norm_num⟩ : Fin 306936) := by
  change _ ↔ _ ∧ p ∉ orbOne
  rw [← inOrbOne_iff]
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

theorem orbit_eq_of_mem {x y p : Fin 306936}
    (hx : p ∈ MulAction.orbit (lvl 1) x) (hy : p ∈ MulAction.orbit (lvl 1) y) :
    MulAction.orbit (lvl 1) x = MulAction.orbit (lvl 1) y :=
  (MulAction.orbit_eq_iff.2 hx).symm.trans (MulAction.orbit_eq_iff.2 hy)

theorem two_mem_orbit {p : Fin 306936} (h : subLab p = 2) :
    p ∈ MulAction.orbit (lvl 1) (⟨CFSG.Sporadic.Fi24.Native.subRoot, by decide⟩ : Fin 306936) := by
  classical
  obtain ⟨h0, h1⟩ := subLab_eq_two.1 h
  by_contra h2
  have hdisj : Disjoint orbOne orbTwo := by
    rw [Set.disjoint_left]
    intro q hq1 hq2
    have e := orbit_eq_of_mem hq1 hq2
    have := card_orbOne
    rw [orbOne, e, ← orbTwo, card_orbTwo] at this
    exact absurd this (by norm_num)
  have hroot1 : root ∉ orbOne := fun hr => not_root_of_orbit (by decide) hr rfl
  have hroot2 : root ∉ orbTwo := fun hr => not_root_of_orbit (by decide) hr rfl
  set U : Set (Fin 306936) := insert p (insert root (orbOne ∪ orbTwo)) with hU
  have hfin1 : orbOne.Finite := Set.toFinite _
  have hfin2 : orbTwo.Finite := Set.toFinite _
  have hcU : U.ncard = 306937 := by
    rw [hU, Set.ncard_insert_of_notMem (by
        rintro (e | e | e)
        · exact h0 e
        · exact h1 e
        · exact h2 e) (Set.toFinite _),
      Set.ncard_insert_of_notMem (by
        rintro (e | e)
        · exact hroot1 e
        · exact hroot2 e) (Set.toFinite _),
      Set.ncard_union_eq hdisj hfin1 hfin2, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
      card_orbOne, card_orbTwo]
  have hle : U.ncard ≤ 306936 := by
    have := Set.ncard_le_ncard (Set.subset_univ U) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_fin] at this
  omega

theorem subLab_inv :
    ∀ h ∈ lvl 1, ∀ p : Fin 306936, subLab (h • p) = subLab p := by
  intro h hh p
  have hinv : h⁻¹ ∈ lvl 1 := (lvl 1).inv_mem hh
  by_cases hp0 : p = root
  · rw [hp0, lvl_one_fix hh]
  by_cases hp1 : p ∈ MulAction.orbit (lvl 1) (⟨305530, by norm_num⟩ : Fin 306936)
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
    ∀ p q : Fin 306936, subLab p = subLab q → ∃ h ∈ lvl 1, h • p = q := by
  intro p q hpq
  have key : ∀ {x : Fin 306936} {H : Subgroup J}, p ∈ MulAction.orbit H x →
      q ∈ MulAction.orbit H x → ∃ h ∈ H, h • p = q := by
    intro x H hp hq
    obtain ⟨⟨u, hu⟩, rfl⟩ := hp
    obtain ⟨⟨v, hv⟩, rfl⟩ := hq
    refine ⟨v * u⁻¹, H.mul_mem hv (H.inv_mem hu), ?_⟩
    change (v * u⁻¹) • (u • x) = v • x
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
    (Finset.univ.filter (fun p : Fin 306936 => subLab p = 1)).card = 275264 := by
  classical
  have hc := card_orbOne
  have hset : orbOne = ↑(Finset.univ.filter (fun p : Fin 306936 => subLab p = 1)) := by
    ext p
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    exact subLab_eq_one.symm
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
  exact hc

theorem card_subLab_two :
    (Finset.univ.filter (fun p : Fin 306936 => subLab p = 2)).card = 31671 := by
  have h := Finset.card_eq_sum_card_fiberwise (f := subLab) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin] at h
  have h0 : (Finset.univ.filter (fun p : Fin 306936 => subLab p = 0)).card = 1 :=
    card_subLab_zero
  have h1 : (Finset.univ.filter (fun p : Fin 306936 => subLab p = 1)).card = 275264 :=
    card_subLab_one
  omega

theorem card_subLab (i : Fin 3) :
    (Finset.univ.filter (fun p : Fin 306936 => subLab p = i)).card = subSizes i := by
  fin_cases i
  · exact card_subLab_zero
  · exact card_subLab_one
  · exact card_subLab_two

instance isPreprimitive :
    MulAction.IsPreprimitive J (Fin 306936) := by
  apply isPreprimitive_of_suborbit_labels root (lvl 1) (fun h hh => lvl_one_fix hh) subLab
    subLab_inv subLab_orb
  intro S hS hdvd
  have h0 : subLab root = 0 := subLab_eq_zero.2 rfl
  rw [h0] at hS ⊢
  have hsum : (∑ i ∈ S, (Finset.univ.filter (fun p : Fin 306936 => subLab p = i)).card) =
      ∑ i ∈ S, subSizes i := Finset.sum_congr rfl fun i _ => card_subLab i
  rw [hsum, Fintype.card_fin] at hdvd
  exact subSizes_blocks S hS hdvd

theorem isSimpleGroup_J : IsSimpleGroup J := by
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Fin 306936) ?_ a b closure_ab root
    ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  · rw [orderOf_a, orderOf_b]; norm_num
  · rw [orderOf_ab, card_stabilizer_root]; norm_num

theorem isSimpleGroup_Fi24prime :
    IsSimpleGroup Blueprint.NativeSporadic.Fi24prime :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J fi24EquivJ

theorem card_Fi24prime :
    Nat.card Blueprint.NativeSporadic.Fi24prime = 1255205709190661721292800 := by
  rw [Nat.card_congr fi24EquivJ.toEquiv, card_J]

end CFSG.Sporadic.Fi24
