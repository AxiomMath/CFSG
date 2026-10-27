module

public import CFSG.Quasithin.Recognition.RuRank3RuIso
public import CFSG.Quasithin.Recognition.RuRank3RuGraphData

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem ncard_setOf_fin (n : ℕ) (p : ℕ → Bool) :
    {x : Fin n | p x = true}.ncard = (List.range n).countP p := by
  classical
  have e : {x : Fin n | p x = true} =
      ((Finset.univ.filter fun x : Fin n => p x = true) : Set (Fin n)) := by
    ext x
    simp
  rw [e, Set.ncard_coe_finset, List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  apply Finset.card_bij (fun (y : Fin n) _ => (y : ℕ))
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp [hy, y.2]
  · intro a _ b _ h
    exact Fin.ext h
  · intro m hm
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range] at hm
    exact ⟨⟨m, hm.1⟩, by simpa using hm.2, rfl⟩

theorem genSubgroup_invariant {n k : ℕ} {Gs : ℕ → Equiv.Perm (Fin n)} {T : Set (Fin n)}
    (hT : ∀ i < k, ∀ x, Gs i x ∈ T ↔ x ∈ T) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ genSubgroup n k Gs) : ∀ x, g x ∈ T ↔ x ∈ T := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, hi, rfl⟩ := hg
    exact hT i hi
  | one => intro x; rfl
  | mul g h _ _ ihg ihh => intro x; rw [Equiv.Perm.mul_apply, ihg, ihh]
  | inv g _ ihg =>
    intro x
    rw [← ihg (g⁻¹ x), perm_apply_inv]

theorem exists_bool_of_invariant {n m : ℕ} {gens : Array (Array ℕ)}
    {Gs : ℕ → Equiv.Perm (Fin n)} {lab : Array ℕ} (hlab : lab = (orbLabels n gens).1)
    (hrep : ∀ k < gens.size, Rep n gens[k]! (Gs k)) (h : orbCheck n gens = true)
    (hm : ∀ x : Fin n, lab[(x : ℕ)]! < m) {T : Set (Fin n)}
    (hT : ∀ k < gens.size, ∀ x, Gs k x ∈ T ↔ x ∈ T) :
    ∃ b : Fin m → Bool, ∀ x : Fin n, x ∈ T ↔ bAt b lab[(x : ℕ)]! = true := by
  classical
  subst hlab
  refine ⟨fun l => decide (∃ y ∈ T, (orbLabels n gens).1[(y : ℕ)]! = l), fun x => ?_⟩
  simp only [bAt, hm x, ↓reduceDIte, decide_eq_true_eq]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    have hmem : x ∈ MulAction.orbit (genSubgroup n gens.size Gs) y := by
      rw [orbit_eq_labels hrep h y]
      exact hxy.symm
    obtain ⟨g, rfl⟩ := hmem
    exact (genSubgroup_invariant hT g.2 y).2 hy

theorem ncard_eq_selCount {n m : ℕ} {lab : Array ℕ} {b : Fin m → Bool} {T : Set (Fin n)}
    (hT : ∀ x : Fin n, x ∈ T ↔ bAt b lab[(x : ℕ)]! = true) : T.ncard = selCount n lab b := by
  have e : T = {x : Fin n | bAt b lab[(x : ℕ)]! = true} := Set.ext hT
  rw [e]
  exact ncard_setOf_fin n fun y => bAt b lab[y]!

theorem ruR0Arrs_get {k : ℕ} (hk : k < 4) : ruR0Arrs[k]! = ruR0Arr k := by
  rw [ruR0Arrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem ruR0Arrs_size : ruR0Arrs.size = 4 := by simp [ruR0Arrs]

theorem ruR0Arrs_rep
    : ∀ k < ruR0Arrs.size, Rep 4060 ruR0Arrs[k]! (ruR0Gen k) := by
  intro k hk
  rw [ruR0Arrs_size] at hk
  rw [ruR0Arrs_get hk]
  exact rep_ruR0Gen hk

theorem genSubgroup_ruR0
    : genSubgroup 4060 ruR0Arrs.size ruR0Gen = ruR0 := by
  rw [← ruQ_eq_R0, genSubgroup, ruQ, ruR0Arrs_size]
  congr 1
  ext g
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, rfl⟩

theorem orbit_ruR0
    (x : Fin 4060) :
    MulAction.orbit ruR0 x = {y : Fin 4060 | ruQLab[(y : ℕ)]! = ruQLab[(x : ℕ)]!} := by
  rw [← genSubgroup_ruR0]
  exact orbit_eq_orbLab ruR0Arrs_rep ruQ_check.1 x

theorem ruQLab_ruB
    (j : Fin 1755) : ruQLab[((ruB j : Fin 4060) : ℕ)]! = ruQLab[1]! := by
  rw [ruB_val]
  have := allLt_spec ruQ_check.2.2.1 j.2
  rwa [beq_iff_eq] at this

theorem range_ruB_eq
    : Set.range ruB = {y : Fin 4060 | ruQLab[(y : ℕ)]! = ruQLab[1]!} := by
  have hsub : Set.range ruB ⊆ {y : Fin 4060 | ruQLab[(y : ℕ)]! = ruQLab[1]!} := by
    rintro _ ⟨j, rfl⟩
    exact ruQLab_ruB j
  refine Set.eq_of_subset_of_ncard_le hsub ?_
  rw [Set.ncard_range_of_injective ruB_injective, Nat.card_eq_fintype_card, Fintype.card_fin,
    ncard_labelClass, ruQ_check.2.2.2.1]

theorem mem_range_ruB_iff
    (x : Fin 4060) : x ∈ Set.range ruB ↔ ruQLab[(x : ℕ)]! = ruQLab[1]! := by
  rw [range_ruB_eq]
  rfl

@[expose] def ruG0F : Fin 4060 := ⟨2808, by norm_num⟩

theorem ruG0F_val : (ruG0F : ℕ) = ruG0 := rfl

@[expose] def ruS : Set (Fin 4060) := {x | x ≠ 0 ∧ x ∉ Set.range ruB}

theorem ruQLab_eq_zero_iff
    (x : Fin 4060) : ruQLab[(x : ℕ)]! = ruQLab[0]! ↔ x = 0 := by
  constructor
  · intro h
    have := allLt_spec ruQ_check.2.1 x.2
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    rcases this with h0 | h0
    · exact Fin.ext h0
    · exact absurd h h0
  · rintro rfl
    rfl

theorem mem_ruS_iff
    (x : Fin 4060) : x ∈ ruS ↔ ruQLab[(x : ℕ)]! = ruQLab[ruG0]! := by
  have htri := allLt_spec ruQ_check.2.2.2.2.2.1 x.2
  simp only [Bool.or_eq_true, beq_iff_eq] at htri
  constructor
  · rintro ⟨h0, hD⟩
    rcases htri with (h | h) | h
    · exact absurd ((ruQLab_eq_zero_iff x).1 h) h0
    · exact absurd ((mem_range_ruB_iff x).2 h) hD
    · exact h
  · intro h
    refine ⟨fun h0 => ?_, fun hD => ?_⟩
    · subst h0
      exact ruQ_check.2.2.2.2.2.2.2.1 h
    · rw [mem_range_ruB_iff] at hD
      exact ruQ_check.2.2.2.2.2.2.1 (hD.symm.trans h)

theorem ruG0F_mem_ruS
    : ruG0F ∈ ruS := (mem_ruS_iff ruG0F).2 rfl

theorem ruS_eq
    : ruS = {y : Fin 4060 | ruQLab[(y : ℕ)]! = ruQLab[ruG0]!} :=
  Set.ext mem_ruS_iff

theorem ncard_ruS :
    ruS.ncard = 2304 := by
  rw [ruS_eq, ncard_labelClass, ruQ_check.2.2.2.2.1]

theorem orbit_ruR0_one
    : MulAction.orbit ruR0 (1 : Fin 4060) = Set.range ruB := by
  rw [orbit_ruR0, range_ruB_eq]
  rfl

theorem orbit_ruR0_g0
    : MulAction.orbit ruR0 ruG0F = ruS := by
  rw [orbit_ruR0, ruS_eq]
  rfl

theorem exists_ruR0_one
    {d : Fin 4060} (hd : d ∈ Set.range ruB) :
    ∃ p ∈ ruR0, p 1 = d := by
  rw [← orbit_ruR0_one] at hd
  obtain ⟨p, rfl⟩ := hd
  exact ⟨p, p.2, rfl⟩

theorem exists_ruR0_g0
    {s : Fin 4060} (hs : s ∈ ruS) : ∃ p ∈ ruR0, p ruG0F = s := by
  rw [← orbit_ruR0_g0] at hs
  obtain ⟨p, rfl⟩ := hs
  exact ⟨p, p.2, rfl⟩

theorem ruR0_apply_zero {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruR0) : g 0 = 0 :=
  (Subgroup.mem_inf.1 hg).2

theorem ruR0_le_ruP : ruR0 ≤ ruP := inf_le_left

theorem ruR0_mem_range_ruB_iff
    {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruR0) (x : Fin 4060) :
    g x ∈ Set.range ruB ↔ x ∈ Set.range ruB :=
  ruR0_le_DStab hg x

theorem ruR0_mem_ruS_iff
    {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruR0) (x : Fin 4060) :
    g x ∈ ruS ↔ x ∈ ruS := by
  have h0 : g x = 0 ↔ x = 0 := by
    constructor
    · intro h
      apply g.injective
      rw [h, ruR0_apply_zero hg]
    · rintro rfl
      exact ruR0_apply_zero hg
  show (g x ≠ 0 ∧ g x ∉ Set.range ruB) ↔ (x ≠ 0 ∧ x ∉ Set.range ruB)
  rw [ne_eq, ne_eq, h0, ruR0_mem_range_ruB_iff hg]

@[expose] def ruAdj (x y : Fin 4060) : Prop := ∃ g ∈ ruP, g 0 = x ∧ g 1 = y

theorem ruAdj_apply {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP) (x y : Fin 4060) :
    ruAdj (g x) (g y) ↔ ruAdj x y := by
  constructor
  · rintro ⟨h, hh, h0, h1⟩
    refine ⟨g⁻¹ * h, mul_mem (inv_mem hg) hh, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, h0, perm_inv_apply]
    · rw [Equiv.Perm.mul_apply, h1, perm_inv_apply]
  · rintro ⟨h, hh, rfl, rfl⟩
    exact ⟨g * h, mul_mem hg hh, rfl, rfl⟩

theorem ruA0_zero : ruA0 0 = 1 := by
  apply Fin.ext
  rw [← rep_ruA0 0]
  exact ruA0_check.1

theorem ruA0_one : ruA0 1 = 0 := by
  apply Fin.ext
  rw [← rep_ruA0 1]
  exact ruA0_check.2

theorem ruA0_mem : ruA0 ∈ ruP := Subgroup.subset_closure (Set.mem_insert _ _)

theorem mul_ruA0_zero
    (g : Equiv.Perm (Fin 4060)) : (g * ruA0) 0 = g 1 := by
  rw [Equiv.Perm.mul_apply, ruA0_zero]

theorem mul_ruA0_one
    (g : Equiv.Perm (Fin 4060)) : (g * ruA0) 1 = g 0 := by
  rw [Equiv.Perm.mul_apply, ruA0_one]

theorem ruAdj_symm
    {x y : Fin 4060} (h : ruAdj x y) : ruAdj y x := by
  obtain ⟨g, hg, rfl, rfl⟩ := h
  exact ⟨g * ruA0, mul_mem hg ruA0_mem, mul_ruA0_zero g, mul_ruA0_one g⟩

theorem ruAdj_comm
    (x y : Fin 4060) : ruAdj x y ↔ ruAdj y x := ⟨ruAdj_symm, ruAdj_symm⟩

theorem ruAdj_zero_iff
    (y : Fin 4060) : ruAdj 0 y ↔ y ∈ Set.range ruB := by
  rw [← orbit_ruR0_one]
  constructor
  · rintro ⟨g, hg, h0, rfl⟩
    have hg0 : g ∈ ruR0 := Subgroup.mem_inf.2 ⟨hg, by
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact h0⟩
    exact ⟨⟨g, hg0⟩, rfl⟩
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g, ruR0_le_ruP hg, ruR0_apply_zero hg, rfl⟩

theorem not_ruAdj_self (x : Fin 4060) : ¬ ruAdj x x := by
  intro h
  obtain ⟨g, hg, h0, h1⟩ := h
  have := g.injective (h0.trans h1.symm)
  exact absurd this (by decide)

theorem ruAdj_iff_tree
    (v x : Fin 4060) :
    ruAdj v x ↔ (ruTreeElt v)⁻¹ x ∈ Set.range ruB := by
  rw [← ruAdj_zero_iff]
  conv_lhs => rw [← ruTreeElt_apply_zero v, ← perm_apply_inv (ruTreeElt v) x]
  exact ruAdj_apply (ruTreeElt_mem v) _ _

theorem ruRowA_spec
    {v : Fin 4060} {ti : Array ℕ} (h : isInvA 4060 (ruTreeArr v) ti = true)
    (x : Fin 4060) : ruRowA ti x = true ↔ ruAdj v x := by
  have hrep : Rep 4060 ti (ruTreeElt v)⁻¹ := rep_inv_of_isInvA (rep_ruTreeElt v.2) h
  rw [ruAdj_iff_tree, mem_range_ruB_iff, ruRowA, beq_iff_eq, hrep x]

theorem ruRowA_one
    (x : Fin 4060) : ruRowA ruTI1 x = true ↔ ruAdj 1 x :=
  ruRowA_spec (v := 1) ruQ_check.2.2.2.2.2.2.2.2.1 x

theorem ruRowA_g0
    (x : Fin 4060) : ruRowA ruTIG0 x = true ↔ ruAdj ruG0F x :=
  ruRowA_spec (v := ruG0F) ruQ_check.2.2.2.2.2.2.2.2.2 x

@[expose] noncomputable def ruFGen (i : ℕ) : Equiv.Perm (Fin 4060) := permOfArr 4060 (ruFGArr i)

theorem ruFG_facts {i : ℕ} (hi : i < 2) :
    isInvA 4060 (ruFGArr i) (invCand 4060 (ruFGArr i)) = true ∧
    ruSift 4060 (ruField4060 3) ruJoinBase (ruFGArr i) = true ∧ (ruFGArr i)[0]! = 0 ∧
    (ruFGArr i)[1]! = 1 := by
  have h := allLt_spec ruStabs_check.1 hi
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem rep_ruFGen
    {i : ℕ} (hi : i < 2) : Rep 4060 (ruFGArr i) (ruFGen i) :=
  (rep_permOfArr (ruFG_facts hi).1).1

theorem ruFGen_mem
    {i : ℕ} (hi : i < 2) : ruFGen i ∈ ruP :=
  mem_ruP_of_sift (rep_ruFGen hi) (ruFG_facts hi).2.1

theorem ruFGen_zero {i : ℕ} (hi : i < 2) : ruFGen i 0 = 0 := by
  apply Fin.ext
  rw [← rep_ruFGen hi 0]
  exact (ruFG_facts hi).2.2.1

theorem ruFGen_one {i : ℕ} (hi : i < 2) : ruFGen i 1 = 1 := by
  apply Fin.ext
  rw [← rep_ruFGen hi 1]
  exact (ruFG_facts hi).2.2.2

theorem ruFGArrs_size : ruFGArrs.size = 2 := by simp [ruFGArrs]

theorem ruFGArrs_rep
    : ∀ k < ruFGArrs.size, Rep 4060 ruFGArrs[k]! (ruFGen k) := by
  intro k hk
  rw [ruFGArrs_size] at hk
  rw [ruFGArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  exact rep_ruFGen hk

theorem ru_rf1_one
    {T : Set (Fin 4060)}
    (hT : ∀ g ∈ ruP, g 0 = 0 → g 1 = 1 → ∀ x, (g x ∈ T ↔ x ∈ T)) (hcard : T.ncard = 1755)
    (h0 : 0 ∈ T) (h1 : 1 ∉ T) : (∀ x, x ∈ T ↔ ruAdj 1 x) ∨ ∀ x ∈ T, x ∉ ruS := by
  have hm : ∀ x : Fin 4060, ruFLab[(x : ℕ)]! < 8 := fun x => by
    have := allLt_spec ruStabs_check.2.2.2.1 x.2
    simpa using this
  have hTg : ∀ k < ruFGArrs.size, ∀ x, ruFGen k x ∈ T ↔ x ∈ T := by
    intro k hk
    rw [ruFGArrs_size] at hk
    exact hT _ (ruFGen_mem hk) (ruFGen_zero hk) (ruFGen_one hk)
  obtain ⟨b, hb⟩ :=
    exists_bool_of_invariant (lab := ruFLab) (orbLab_eq _ _) ruFGArrs_rep ruStabs_check.2.2.1 hm hTg
  have hsel : selCount 4060 ruFLab b = 1755 := by rw [← ncard_eq_selCount hb, hcard]
  have hb0 : bAt b ruFLab[0]! = true := (hb 0).1 h0
  have hb1 : bAt b ruFLab[1]! = false := by
    have := mt (hb 1).2 h1
    simpa using this
  rcases ruRF_check.1 b hsel hb0 hb1 with h | h
  · left
    intro x
    have := allLt_spec h x.2
    rw [beq_iff_eq] at this
    rw [hb x, this, ruRowA_one]
  · right
    intro x hx hS
    have := allLt_spec h x.2
    have hS' : ruInS x = true := by
      rw [ruInS, beq_iff_eq]
      exact (mem_ruS_iff x).1 hS
    rw [(hb x).1 hx, hS'] at this
    simp at this

theorem ru_rf1
    {d : Fin 4060} (hd : d ∈ Set.range ruB) {T : Set (Fin 4060)}
    (hT : ∀ g ∈ ruR0, g d = d → ∀ x, (g x ∈ T ↔ x ∈ T)) (hcard : T.ncard = 1755)
    (h0 : 0 ∈ T) (hdT : d ∉ T) : (∀ x, x ∈ T ↔ ruAdj d x) ∨ ∀ x ∈ T, x ∉ ruS := by
  obtain ⟨p, hp, hp1⟩ := exists_ruR0_one hd
  set T₁ : Set (Fin 4060) := p ⁻¹' T with hT₁
  have hT₁inv : ∀ g ∈ ruP, g 0 = 0 → g 1 = 1 → ∀ x, (g x ∈ T₁ ↔ x ∈ T₁) := by
    intro g hg g0 g1 x
    have hgR : g ∈ ruR0 := Subgroup.mem_inf.2 ⟨hg, by
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact g0⟩
    have hm : p * g * p⁻¹ ∈ ruR0 := mul_mem (mul_mem hp hgR) (inv_mem hp)
    have hfix : (p * g * p⁻¹) d = d := by
      rw [← hp1, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply, g1]
    have := hT _ hm hfix (p x)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply] at this
    exact this
  have hcard₁ : T₁.ncard = 1755 := by
    rw [hT₁, Set.ncard_preimage_of_injective_subset_range p.injective
      (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _), hcard]
  have h0₁ : (0 : Fin 4060) ∈ T₁ := by
    show p 0 ∈ T
    rw [ruR0_apply_zero hp]
    exact h0
  have h1₁ : (1 : Fin 4060) ∉ T₁ := by
    show p 1 ∉ T
    rw [hp1]
    exact hdT
  rcases ru_rf1_one hT₁inv hcard₁ h0₁ h1₁ with h | h
  · left
    intro x
    have e := h (p⁻¹ x)
    rw [hT₁, Set.mem_preimage, perm_apply_inv] at e
    rw [e, ← ruAdj_apply (ruR0_le_ruP hp), perm_apply_inv, hp1]
  · right
    intro x hx hS
    have hx₁ : p⁻¹ x ∈ T₁ := by
      show p (p⁻¹ x) ∈ T
      rw [perm_apply_inv]
      exact hx
    apply h _ hx₁
    rw [← ruR0_mem_ruS_iff hp, perm_apply_inv]
    exact hS

@[expose] noncomputable def ruEGen (i : ℕ) : Equiv.Perm (Fin 4060) := permOfArr 4060 (ruEGArr i)

theorem ruEG_facts {i : ℕ} (hi : i < 2) :
    isInvA 4060 (ruEGArr i) (invCand 4060 (ruEGArr i)) = true ∧
    ruSift 4060 (ruField4060 3) ruJoinBase (ruEGArr i) = true ∧ (ruEGArr i)[0]! = 0 ∧
    (ruEGArr i)[ruG0]! = ruG0 := by
  have h := allLt_spec ruStabs_check.2.1 hi
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem rep_ruEGen
    {i : ℕ} (hi : i < 2) : Rep 4060 (ruEGArr i) (ruEGen i) :=
  (rep_permOfArr (ruEG_facts hi).1).1

theorem ruEGen_mem
    {i : ℕ} (hi : i < 2) : ruEGen i ∈ ruP :=
  mem_ruP_of_sift (rep_ruEGen hi) (ruEG_facts hi).2.1

theorem ruEGen_zero {i : ℕ} (hi : i < 2) : ruEGen i 0 = 0 := by
  apply Fin.ext
  rw [← rep_ruEGen hi 0]
  exact (ruEG_facts hi).2.2.1

theorem ruEGen_g0 {i : ℕ} (hi : i < 2) : ruEGen i ruG0F = ruG0F := by
  apply Fin.ext
  rw [← rep_ruEGen hi ruG0F]
  exact (ruEG_facts hi).2.2.2

theorem ruEGArrs_size : ruEGArrs.size = 2 := by simp [ruEGArrs]

theorem ruEGArrs_rep
    : ∀ k < ruEGArrs.size, Rep 4060 ruEGArrs[k]! (ruEGen k) := by
  intro k hk
  rw [ruEGArrs_size] at hk
  rw [ruEGArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  exact rep_ruEGen hk

theorem ru_rf2_g0
    {T : Set (Fin 4060)}
    (hT : ∀ g ∈ ruP, g 0 = 0 → g ruG0F = ruG0F → ∀ x, (g x ∈ T ↔ x ∈ T))
    (hcard : T.ncard = 1755) (h0 : 0 ∉ T) (hg0 : ruG0F ∉ T) :
    (∀ x, x ∈ T ↔ ruAdj ruG0F x) ∨ ∀ x, x ∈ T ↔ x ∈ Set.range ruB := by
  have hm : ∀ x : Fin 4060, ruELab[(x : ℕ)]! < 9 := fun x => by
    have := allLt_spec ruStabs_check.2.2.2.2.2 x.2
    simpa using this
  have hTg : ∀ k < ruEGArrs.size, ∀ x, ruEGen k x ∈ T ↔ x ∈ T := by
    intro k hk
    rw [ruEGArrs_size] at hk
    exact hT _ (ruEGen_mem hk) (ruEGen_zero hk) (ruEGen_g0 hk)
  obtain ⟨b, hb⟩ :=
    exists_bool_of_invariant (lab := ruELab) (orbLab_eq _ _) ruEGArrs_rep ruStabs_check.2.2.2.2.1 hm hTg
  have hsel : selCount 4060 ruELab b = 1755 := by rw [← ncard_eq_selCount hb, hcard]
  have hb0 : bAt b ruELab[0]! = false := by
    have := mt (hb 0).2 h0
    simpa using this
  have hbg : bAt b ruELab[ruG0]! = false := by
    have := mt (hb ruG0F).2 hg0
    simpa [ruG0F_val] using this
  rcases ruRF_check.2 b hsel hb0 hbg with h | h
  · left
    intro x
    have := allLt_spec h x.2
    rw [beq_iff_eq] at this
    rw [hb x, this, ruRowA_g0]
  · right
    intro x
    have := allLt_spec h x.2
    rw [beq_iff_eq] at this
    rw [hb x, this, mem_range_ruB_iff, beq_iff_eq]

theorem ru_rf2
    {s : Fin 4060} (hs : s ∈ ruS) {T : Set (Fin 4060)}
    (hT : ∀ g ∈ ruR0, g s = s → ∀ x, (g x ∈ T ↔ x ∈ T)) (hcard : T.ncard = 1755)
    (h0 : 0 ∉ T) (hsT : s ∉ T) :
    (∀ x, x ∈ T ↔ ruAdj s x) ∨ ∀ x, x ∈ T ↔ x ∈ Set.range ruB := by
  obtain ⟨p, hp, hpg⟩ := exists_ruR0_g0 hs
  set T₁ : Set (Fin 4060) := p ⁻¹' T with hT₁
  have hT₁inv : ∀ g ∈ ruP, g 0 = 0 → g ruG0F = ruG0F → ∀ x, (g x ∈ T₁ ↔ x ∈ T₁) := by
    intro g hg g0 gg x
    have hgR : g ∈ ruR0 := Subgroup.mem_inf.2 ⟨hg, by
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact g0⟩
    have hm : p * g * p⁻¹ ∈ ruR0 := mul_mem (mul_mem hp hgR) (inv_mem hp)
    have hfix : (p * g * p⁻¹) s = s := by
      rw [← hpg, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply, gg]
    have := hT _ hm hfix (p x)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply] at this
    exact this
  have hcard₁ : T₁.ncard = 1755 := by
    rw [hT₁, Set.ncard_preimage_of_injective_subset_range p.injective
      (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _), hcard]
  have h0₁ : (0 : Fin 4060) ∉ T₁ := by
    show p 0 ∉ T
    rw [ruR0_apply_zero hp]
    exact h0
  have hg₁ : ruG0F ∉ T₁ := by
    show p ruG0F ∉ T
    rw [hpg]
    exact hsT
  rcases ru_rf2_g0 hT₁inv hcard₁ h0₁ hg₁ with h | h
  · left
    intro x
    have e := h (p⁻¹ x)
    rw [hT₁, Set.mem_preimage, perm_apply_inv] at e
    rw [e, ← ruAdj_apply (ruR0_le_ruP hp), perm_apply_inv, hpg]
  · right
    intro x
    have e := h (p⁻¹ x)
    rw [hT₁, Set.mem_preimage, perm_apply_inv] at e
    rw [e, ← ruR0_mem_range_ruB_iff hp, perm_apply_inv]

end CFSG.Quasithin.RuRank3
