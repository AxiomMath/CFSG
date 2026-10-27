module

public import CFSG.Sporadic.Recognition.LyonsModelArr
public import CFSG.Sporadic.Recognition.LyonsModelCount
public import CFSG.Sporadic.Recognition.LyonsModelCP3Fact

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly0

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Recognition.McLMultiplier Equiv
  Subgroup

theorem cp3Valid_spec {D : Cp3Data} (h : cp3Valid D = true) :
    D.sets.size = 15400 ∧ D.sets[0]! = fixPts tabYw ∧ D.words[0]! = ([] : List ℤ) ∧
    (∀ a ∈ D.sets, isStrictSet a = true) ∧
    (∀ i < 15400, i ≠ 0 → (D.par[i]!).1 < i ∧ (D.par[i]!).2 < 2 ∧
      D.sets[i]! = applyToSet (gTab (D.par[i]!).2) D.sets[(D.par[i]!).1]! ∧
      D.words[i]! = gLet (D.par[i]!).2 :: D.words[(D.par[i]!).1]!) ∧
    (∀ i < 15400, ∀ j < 2, ∃ k < 15400, D.sets[k]! = applyToSet (gTab j) D.sets[i]!) ∧
    (∀ i < 15400, ∀ i' < 15400, D.sets[i]! = D.sets[i']! → i = i') ∧
    (∀ i < 15400, i = 0 ∨ i ∈ D.orb ∨ isWit D.words[i]! D.wit[i]! = true) ∧
    0 < D.orb.size ∧ (∀ i ∈ D.orb, i < 15400) ∧
    (∀ k < D.orb.size, k ≠ 0 → (D.opar[k]!).1 < k ∧ (D.opar[k]!).2 < uTabs.size ∧
      D.sets[D.orb[k]!]! = applyToSet uTabs[(D.opar[k]!).2]! D.sets[D.orb[(D.opar[k]!).1]!]!) ∧
    D.sets[D.orb[0]!]! = fixPts tabW := by
  unfold cp3Valid at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Array.all_eq_true, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, and_assoc] at h
  obtain ⟨hn, hpar, hwords, hwit, hopar, h0, hw0, hstrict, htree, hclos, hdist, hcomm, horb0,
    horb, hforest, hw⟩ := h
  refine ⟨hn, h0, hw0, ?_, ?_, ?_, ?_, ?_, horb0, ?_, ?_, hw⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ha
    exact hstrict i hi
  · intro i hi hne
    rcases htree i (by omega) with h1 | h1
    · exact absurd h1 hne
    · exact h1
  · intro i hi j hj
    have h1 := hclos i (by omega) j hj
    revert h1
    cases hm : (setIdx D.sets)[applyToSet (gTab j) D.sets[i]!]? with
    | none => simp
    | some k =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      intro h2
      exact ⟨k, by omega, h2.2⟩
  · intro i hi i' hi' he
    have h1 := hdist i (by omega)
    have h2 := hdist i' (by omega)
    rw [he] at h1
    rw [h1] at h2
    exact Option.some.inj h2
  · intro i hi
    rcases hcomm i (by omega) with (h1 | h1) | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl (Array.contains_iff_mem.1 h1))
    · exact Or.inr (Or.inr h1)
  · intro i hi
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hi
    have := horb k hk
    omega
  · intro k hk hne
    rcases hforest k hk with h1 | h1
    · exact absurd h1 hne
    · exact h1

theorem rep_gTab (h : tabCheck = true) {j : ℕ} (hj : j < 2) : Rep deg (gTab j) (gens0 j) :=
  rep_gens0 h j hj

theorem letterG_gLet (j : ℕ) : letterG gens0 (gLet j) = gens0 j := by
  unfold gLet
  rw [letterG_pos gens0 (by omega)]
  simp

theorem rep_letter0 (h : tabCheck = true) {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 2) :
    Rep deg (letterOf tabs0 invs0 l) (letterG gens0 l) :=
  rep_letterOf (rep_gens0 h) (invOK_level0 h) hl

theorem evalPt_eq (h : tabCheck = true) (w : List ℤ) (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2)
    {q : ℕ} (hq : q < deg) : evalPt w q = idx deg (wG gens0 w) q := by
  induction w with
  | nil => simp [evalPt, idx_one]
  | cons l w ih =>
    have ih' := ih (fun l' hl' => hw l' (by simp [hl']))
    have hlt : evalPt w q < deg := by rw [ih']; exact idx_lt _ hq
    have e1 : evalPt (l :: w) q = ap (letterOf tabs0 invs0 l) (evalPt w q) := by
      simp only [evalPt, List.foldr_cons]
    rw [e1, wG_cons, idx_mul, rep_letter0 h (hw l (by simp)) _ hlt, ih']

theorem conjPt_eq (h : tabCheck = true) (g : List ℤ) (hg : ∀ l ∈ g, l ≠ 0 ∧ l.natAbs ≤ 2)
    {q : ℕ} (hq : q < deg) :
    conjPt g q = idx deg (wG gens0 g * y0G * (wG gens0 g)⁻¹) q := by
  have hginv : ∀ l ∈ invW g, l ≠ 0 ∧ l.natAbs ≤ 2 := fun l hl => by
    have := hg (-l) (mem_invW hl)
    simpa using this
  have e1 : evalPt (invW g) q = idx deg (wG gens0 g)⁻¹ q := by
    rw [evalPt_eq h _ hginv hq, wG_invW gens0 (fun l hl => (hg l hl).1)]
  have hlt1 : idx deg (wG gens0 g)⁻¹ q < deg := idx_lt _ hq
  have e2 : ap tabYw (idx deg (wG gens0 g)⁻¹ q) = idx deg y0G (idx deg (wG gens0 g)⁻¹ q) :=
    rep_tabYw h _ hlt1
  have hlt2 : idx deg y0G (idx deg (wG gens0 g)⁻¹ q) < deg := idx_lt _ hlt1
  unfold conjPt
  rw [e1, e2, evalPt_eq h g hg hlt2, ← idx_mul, ← idx_mul]

theorem isWit_spec (h : tabCheck = true) {g : List ℤ} (hg : ∀ l ∈ g, l ≠ 0 ∧ l.natAbs ≤ 2)
    {q : ℕ} (hw : isWit g q = true) :
    ¬ (wG gens0 g * y0G * (wG gens0 g)⁻¹) * y0G = y0G * (wG gens0 g * y0G * (wG gens0 g)⁻¹) := by
  intro hcomm
  unfold isWit at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hw
  obtain ⟨hq, hne⟩ := hw
  apply hne
  have e1 := conjPt_eq h g hg hq
  have hyq : ap tabYw q = idx deg y0G q := rep_tabYw h q hq
  have hlt' : ap tabYw q < deg := by rw [hyq]; exact idx_lt _ hq
  rw [e1, rep_tabYw h _ (idx_lt _ hq), conjPt_eq h g hg hlt', hyq, ← idx_mul, ← idx_mul, hcomm]

section Sets

variable {D : Cp3Data}

theorem words_valid (hv : cp3Valid D = true) :
    ∀ i < 15400, ∀ l ∈ D.words[i]!, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi l hl
    by_cases h0 : i = 0
    · subst h0
      obtain ⟨-, -, hw0, -⟩ := cp3Valid_spec hv
      rw [hw0] at hl
      simp at hl
    · obtain ⟨-, -, -, -, htree, -⟩ := cp3Valid_spec hv
      obtain ⟨hlt, hj, -, hw⟩ := htree i hi h0
      rw [hw] at hl
      rcases List.mem_cons.1 hl with rfl | hl'
      · unfold gLet
        constructor
        · omega
        · omega
      · exact ih _ hlt (by omega) l hl'

theorem gElt_mem_B0 (hv : cp3Valid D = true) {i : ℕ} (hi : i < 15400) :
    wG gens0 D.words[i]! ∈ B0 :=
  wG_mem B0 gens0 2 gens0_mem _ (words_valid hv i hi)

theorem strict_get (hv : cp3Valid D = true) {i : ℕ} (hi : i < 15400) :
    isStrictSet D.sets[i]! = true := by
  obtain ⟨hn, -, -, hs, -⟩ := cp3Valid_spec hv
  have hi' : i < D.sets.size := by omega
  rw [getElem!_pos D.sets i hi']
  exact hs _ (Array.getElem_mem hi')

theorem sets_eq (h : tabCheck = true) (hv : cp3Valid D = true) :
    ∀ i < 15400, setOfArr D.sets[i]! = (wG gens0 D.words[i]!) '' {x | y0G x = x} := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h0 : i = 0
    · subst h0
      obtain ⟨-, hs0, hw0, -⟩ := cp3Valid_spec hv
      rw [hs0, hw0, wG_nil, setOfArr_fixPts (rep_tabYw h)]
      simp
    · obtain ⟨-, -, -, -, htree, -⟩ := cp3Valid_spec hv
      obtain ⟨hlt, hj, hs, hw⟩ := htree i hi h0
      have hp : (D.par[i]!).1 < 15400 := by omega
      rw [hs, hw, wG_cons, letterG_gLet,
        setOfArr_applyToSet (rep_gTab h hj) (isStrictSet_lt (strict_get hv hp)), ih _ hlt hp,
        Set.image_image]
      rfl

def fam (D : Cp3Data) : Set (Set (Fin deg)) := {S | ∃ i < 15400, S = setOfArr D.sets[i]!}

theorem fixSet_mem_fam (h : tabCheck = true) (hv : cp3Valid D = true) :
    {x | y0G x = x} ∈ fam D := by
  refine ⟨0, by norm_num, ?_⟩
  rw [sets_eq h hv 0 (by norm_num)]
  obtain ⟨-, -, hw0, -⟩ := cp3Valid_spec hv
  rw [hw0, wG_nil]
  simp

theorem fam_closed (h : tabCheck = true) (hv : cp3Valid D = true) :
    ∀ g ∈ B0, ∀ S ∈ fam D, g '' S ∈ fam D := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    have key : ∀ j < 2, ∀ S ∈ fam D, (gens0 j) '' S ∈ fam D := by
      intro j hj S hS
      obtain ⟨i, hi, rfl⟩ := hS
      obtain ⟨k, hk, he⟩ := (cp3Valid_spec hv).2.2.2.2.2.1 i hi j hj
      refine ⟨k, hk, ?_⟩
      rw [he, setOfArr_applyToSet (rep_gTab h hj) (isStrictSet_lt (strict_get hv hi))]
    rcases hg with hg | hg
    · rw [hg, ← gens0_zero]
      exact key 0 (by norm_num)
    · rw [Set.mem_singleton_iff.1 hg, ← gens0_one]
      exact key 1 (by norm_num)
  | one => intro S hS; simpa using hS
  | mul a b _ _ ha hb =>
    intro S hS
    have : (a * b) '' S = a '' (b '' S) := by rw [Set.image_image]; rfl
    rw [this]
    exact ha _ (hb S hS)
  | inv a _ ha => exact image_inv_mem_of_image_mem (fam D) a ha

theorem fam_mem (h : tabCheck = true) (hv : cp3Valid D = true) :
    ∀ g ∈ B0, g '' {x | y0G x = x} ∈ fam D := fun g hg =>
  fam_closed h hv g hg _ (fixSet_mem_fam h hv)

theorem fam_cov (h : tabCheck = true) (hv : cp3Valid D = true) :
    ∀ S ∈ fam D, ∃ g ∈ B0, S = g '' {x | y0G x = x} := by
  rintro S ⟨i, hi, rfl⟩
  exact ⟨_, gElt_mem_B0 hv hi, sets_eq h hv i hi⟩

theorem fam_ncard (hv : cp3Valid D = true) : (fam D).ncard = 15400 := by
  have hrange : fam D = Set.range fun i : Fin 15400 => setOfArr D.sets[i.val]! := by
    ext S
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, rfl⟩
  have hinj : Function.Injective fun i : Fin 15400 => setOfArr D.sets[i.val]! := by
    intro i i' he
    have h1 := setOfArr_inj (strict_get hv i.isLt) (strict_get hv i'.isLt) he
    exact Fin.ext ((cp3Valid_spec hv).2.2.2.2.2.2.1 i.val i.isLt i'.val i'.isLt h1)
  rw [hrange, Set.ncard_range_of_injective hinj]
  simp

end Sets

abbrev UYperm : Subgroup (Perm (Fin deg)) := closure (Set.range fun j : Fin 4 => uG j.val)

theorem uTabs_size : uTabs.size = 4 := by simp [uTabs, uWords]

theorem UYperm_le_B0 : UYperm ≤ B0 := by
  refine (closure_le B0).2 ?_
  rintro _ ⟨j, rfl⟩
  exact uG_mem_B0 j.val

theorem gcG_mem_B0 : gcG ∈ B0 := by
  rw [gcG_def]
  exact wG_mem B0 gens0 2 gens0_mem _ (decodeWord_mem _)

section Orbit

variable {D : Cp3Data}

theorem orb_get_lt (hv : cp3Valid D = true) {k : ℕ} (hk : k < D.orb.size) : D.orb[k]! < 15400 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, horb, -⟩ := cp3Valid_spec hv
  apply horb
  rw [getElem!_pos D.orb k hk]
  exact Array.getElem_mem hk

theorem orb_forest (h : tabCheck = true) (hv : cp3Valid D = true) :
    ∀ k < D.orb.size, ∃ u ∈ UYperm,
      setOfArr D.sets[D.orb[k]!]! = u '' setOfArr D.sets[D.orb[0]!]! := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h0 : k = 0
    · subst h0
      exact ⟨1, one_mem _, by simp⟩
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, hforest, -⟩ := cp3Valid_spec hv
      obtain ⟨hq, hj, hs⟩ := hforest k hk h0
      rw [uTabs_size] at hj
      have hqk : (D.opar[k]!).1 < D.orb.size := by omega
      obtain ⟨u, hu, hue⟩ := ih _ hq hqk
      refine ⟨uG (D.opar[k]!).2 * u, mul_mem (subset_closure ⟨⟨(D.opar[k]!).2, hj⟩, rfl⟩) hu, ?_⟩
      rw [hs, setOfArr_applyToSet (rep_uTabs h hj)
        (isStrictSet_lt (strict_get hv (orb_get_lt hv hqk))), hue, Set.image_image]
      rfl

end Orbit

theorem fix_conj (g y : Perm (Fin deg)) :
    {i | (g * y * g⁻¹) i = i} = g '' {i | y i = i} := by
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_image, Equiv.Perm.mul_apply]
  constructor
  · intro hi
    refine ⟨g⁻¹ i, ?_, by simp⟩
    have h2 := congrArg (⇑(g⁻¹ : Perm (Fin deg))) hi
    simpa using h2
  · rintro ⟨j, hj, rfl⟩
    simp [hj]

theorem fix_inv (y : Perm (Fin deg)) :
    {i | (y⁻¹ : Perm (Fin deg)) i = i} = {i | y i = i} := by
  ext i
  show (y⁻¹ : Perm (Fin deg)) i = i ↔ y i = i
  rw [Equiv.Perm.inv_eq_iff_eq, eq_comm]

theorem conj_y0G_of_mem_normalizer (h : tabCheck = true) (hs : structCheck = true)
    (hc1 : cp1Check = true) {n : Perm (Fin deg)}
    (hn : n ∈ normalizer (zpowers y0G : Set (Perm (Fin deg)))) :
    n * y0G * n⁻¹ = y0G ∨ n * y0G * n⁻¹ = y0G⁻¹ := by
  obtain ⟨-, h3, h1, -⟩ := cp1_facts h hs hc1
  have hfin : IsOfFinOrder y0G := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, h3⟩
  have hmem := (mem_normalizer_zpowers_iff_of_isOfFinOrder hfin).1 hn
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  rcases zpow_cases h3 k with e | e | e
  · exfalso
    apply h1
    have : n * y0G * n⁻¹ = 1 := by rw [← hk, e]
    have h2 : y0G = n⁻¹ * (n * y0G * n⁻¹) * n := by group
    rw [h2, this]
    group
  · left; rw [← hk, e]
  · right
    rw [← hk, e]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact h3

theorem cp3_perm (hv : Cp3Fact) (hB : Nat.card B0 = 5388768000)
    (hN : Nat.card ↥(B0 ⊓ normalizer (zpowers y0G : Set (Perm (Fin deg)))) = 349920)
    {g w : Perm (Fin deg)} (hg : g ∈ B0) (hw : w = g * y0G * g⁻¹) (hcomm : w * y0G = y0G * w)
    (hne1 : w ≠ y0G) (hne2 : w ≠ y0G⁻¹) :
    ∃ u ∈ UYperm, u * w * u⁻¹ = w0G ∨ u * w * u⁻¹ = w0G⁻¹ :=
  hv hB hN g hg w hw hcomm hne1 hne2

theorem mem_zpowers_B0_iff {a : B0} {x : B0} {a' x' : Perm (Fin deg)}
    (ha : (a : Perm (Fin deg)) = a') (hx : (x : Perm (Fin deg)) = x') :
    x ∈ zpowers a ↔ x' ∈ zpowers a' := by
  subst ha hx
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem mem_Y0_iff (h : tabCheck = true) (hs : structCheck = true) (hc1 : cp1Check = true)
    {b : B0} :
    b ∈ Y0 ↔ (b : Perm (Fin deg)) ∈ normalizer (zpowers y0G : Set (Perm (Fin deg))) := by
  obtain ⟨-, h3, -⟩ := cp1_facts h hs hc1
  have hf1 : IsOfFinOrder y0G := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, h3⟩
  have hf2 : IsOfFinOrder yB := by
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, coe_yB]
    exact h3
  rw [mem_normalizer_zpowers_iff_of_isOfFinOrder hf1,
    mem_normalizer_zpowers_iff_of_isOfFinOrder hf2,
    mem_zpowers_B0_iff (a := yB) (x := b * yB * b⁻¹) rfl rfl]
  rfl

theorem UYperm_le_normalizer (h : tabCheck = true) (hs : structCheck = true)
    (hc1 : cp1Check = true) (hi : invCheck = true) :
    UYperm ≤ normalizer (zpowers y0G : Set (Perm (Fin deg))) := by
  obtain ⟨-, h3, -⟩ := cp1_facts h hs hc1
  have hf1 : IsOfFinOrder y0G := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, h3⟩
  obtain ⟨-, -, -, hu⟩ := invCheck_spec h hs hi
  refine (closure_le _).2 ?_
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, mem_normalizer_zpowers_iff_of_isOfFinOrder hf1]
  show uG j.val * y0G * (uG j.val)⁻¹ ∈ zpowers y0G
  rw [mul_assoc]
  rcases hu j.val j.isLt with e | e
  · rw [e]; exact mem_zpowers _
  · rw [e]; exact inv_mem (mem_zpowers _)

theorem UY_le_Y0 (h : tabCheck = true) (hs : structCheck = true) (hc1 : cp1Check = true)
    (hi : invCheck = true) : UY ≤ Y0 := by
  intro b hb
  rw [mem_Y0_iff h hs hc1]
  exact UYperm_le_normalizer h hs hc1 hi hb

section


theorem cp3_model (h : tabCheck = true) (hc : coverCheck = true) (hs : structCheck = true)
    (hc1 : cp1Check = true) (hv : Cp3Fact) {g w : B0} (hw : w = g * yB * g⁻¹)
    (hy : w * yB = yB * w) (hne1 : w ≠ yB) (hne2 : w ≠ yB⁻¹)
    (hN : Nat.card ↥(normalizer (zpowers yB : Set B0)) = 349920) :
    ∃ u ∈ UY, u * w * u⁻¹ = wB ∨ u * w * u⁻¹ = wB⁻¹ := by
  have hN' : Nat.card ↥(B0 ⊓ normalizer (zpowers y0G : Set (Perm (Fin deg)))) = 349920 := by
    rw [← hN]
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, (mem_Y0_iff h hs hc1).2 x.2.2⟩
        invFun := fun b => ⟨b.1.1, b.1.2, (mem_Y0_iff h hs hc1).1 b.2⟩
        left_inv := fun x => rfl
        right_inv := fun b => rfl }
  have hw' : (w : Perm (Fin deg)) = (g : Perm (Fin deg)) * y0G * (g : Perm (Fin deg))⁻¹ := by
    rw [hw]; rfl
  have hy' : (w : Perm (Fin deg)) * y0G = y0G * (w : Perm (Fin deg)) := by
    have := congrArg Subtype.val hy
    exact this
  have hne1' : (w : Perm (Fin deg)) ≠ y0G := fun e => hne1 (Subtype.ext e)
  have hne2' : (w : Perm (Fin deg)) ≠ y0G⁻¹ := fun e => hne2 (Subtype.ext e)
  obtain ⟨u, hu, hue⟩ := cp3_perm hv (card_B0 h hc hs) hN' g.2 hw' hy' hne1' hne2'
  refine ⟨⟨u, UYperm_le_B0 hu⟩, hu, ?_⟩
  rcases hue with e | e
  · left; exact Subtype.ext e
  · right; exact Subtype.ext e

end

end CFSG.Sporadic.Recognition.LyonsSims.Ly0
