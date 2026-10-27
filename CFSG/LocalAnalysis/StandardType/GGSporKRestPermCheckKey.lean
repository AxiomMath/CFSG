module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheckMat

public section

namespace CFSG.StandardType.SporadicShape.PermCover

open Equiv

@[expose] def keyOf {n : ℕ} (B : List ℕ) (x : Perm (Fin n)) : List ℕ :=
  B.map fun i => if h : i < n then (x ⟨i, h⟩).val else 0

@[expose] def keyEq {n : ℕ} (B : List ℕ) (x y : Perm (Fin n)) : Bool :=
  decide (keyOf B x = keyOf B y)

@[expose] def IsBase {n : ℕ} (B : List ℕ) (H : Subgroup (Perm (Fin n))) : Prop :=
  ∀ g ∈ H, (∀ i ∈ B, ∀ h : i < n, g ⟨i, h⟩ = ⟨i, h⟩) → g = 1

theorem eq_of_keyOf_eq {n : ℕ} {B : List ℕ} {H : Subgroup (Perm (Fin n))} (hB : IsBase B H)
    {x y : Perm (Fin n)} (hx : x ∈ H) (hy : y ∈ H) (h : keyOf B x = keyOf B y) : x = y := by
  have key_apply : ∀ {i : ℕ} (hi : i ∈ B) (hn : i < n), x ⟨i, hn⟩ = y ⟨i, hn⟩ := by
    intro i hi hn
    obtain ⟨k, hk, hBk⟩ := List.getElem_of_mem hi
    have h1 : (keyOf B x)[k]? = (keyOf B y)[k]? := by rw [h]
    simp only [keyOf, List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some] at h1
    have hBkn : B[k] < n := by rw [hBk]; exact hn
    simp only [dif_pos hBkn] at h1
    have hxy : x ⟨B[k], hBkn⟩ = y ⟨B[k], hBkn⟩ := Fin.ext (Option.some.inj h1)
    have hfin : (⟨B[k], hBkn⟩ : Fin n) = ⟨i, hn⟩ := Fin.ext hBk
    rw [hfin] at hxy
    exact hxy
  refine inv_mul_eq_one.mp (hB (x⁻¹ * y) (H.mul_mem (H.inv_mem hx) hy) ?_)
  intro i hi hn
  show (x⁻¹ * y) ⟨i, hn⟩ = ⟨i, hn⟩
  rw [Equiv.Perm.mul_apply, ← key_apply hi hn, Equiv.Perm.inv_def]
  exact Equiv.symm_apply_apply x ⟨i, hn⟩

@[expose] def tabK {n : ℕ} (sg : List (Perm (Fin n))) (d : Data) : List (Perm (Fin n)) :=
  d.tabW.map fun w => sporKRestEval sg (sporKRestParse w)

@[expose] def lettersK {n : ℕ} (sg : List (Perm (Fin n))) (a b : Perm (Fin n)) (c : ClassData) :
    List (Perm (Fin n)) :=
  sg ++ c.ent.flatMap fun e => e.zs.map fun w => mat (sporKRestEval [a, b] (sporKRestParse w))

@[expose] def tableOkK {n : ℕ} (B : List ℕ) (sylowOrder : ℕ) (sg tab : List (Perm (Fin n))) : Bool :=
  let keys := tab.map (keyOf B)
  decide (tab.length = sylowOrder) && decide keys.Nodup && keyEq B (tab.getD 0 1) 1 &&
  keys.contains (keyOf B (1 : Perm (Fin n))) &&
  tab.all (fun t => sg.all fun g =>
    keys.contains (keyOf B (t * g)) && keys.contains (keyOf B (t * g⁻¹)))

@[expose] def classesOkK {n : ℕ} (B : List ℕ) (a b : Perm (Fin n)) (d : Data) (sg tab : List (Perm (Fin n))) :
    Bool :=
  d.classes.all (fun c =>
    let r := repMat a b c
    let ls := lettersK sg a b c
    c.ent.all (fun e => decide (e.idx < tab.length) &&
      keyEq B ((sporKRestEval [a, b] (sporKRestParse e.h))⁻¹ * r * sporKRestEval [a, b] (sporKRestParse e.h))
        (tab.getD e.idx 1) &&
      e.zs.all fun zw => keyEq B (sporKRestEval [a, b] (sporKRestParse zw) * tab.getD e.idx 1)
        (tab.getD e.idx 1 * sporKRestEval [a, b] (sporKRestParse zw))) &&
    keyEq B (sporKRestEval ls (sporKRestParse c.wa)) a && keyEq B (sporKRestEval ls (sporKRestParse c.wb)) b)

@[expose] def censusOkK {n : ℕ} (B : List ℕ) (a b : Perm (Fin n)) (d : Data) (reps tab : List (Perm (Fin n))) :
    Bool :=
  d.census.all (fun e => decide (e.cls < d.classes.length) && decide (e.t < tab.length) &&
    decide (e.t ≠ 0) &&
    keyEq B ((sporKRestEval [a, b] (sporKRestParse e.g))⁻¹ * reps.getD e.cls 1 *
      sporKRestEval [a, b] (sporKRestParse e.g)) (tab.getD e.t 1))

@[expose] def checkMatK {n : ℕ} (B : List ℕ) (a b : Perm (Fin n)) (sylowOrder : ℕ) (d : Data) : Bool :=
  let a := mat a
  let b := mat b
  let sg := sgMat a b d
  let tab := tabK sg d
  let reps := d.classes.map (repMat a b)
  let good := goodOf d tab.length
  tableOkK B sylowOrder sg tab && classesOkK B a b d sg tab && censusOkK B a b d reps tab &&
  (List.range tab.length).all fun i => decide (i = 0) || good.getD i false

@[expose] def checkPowMatK {n : ℕ} (B : List ℕ) (p : ℕ) (a b : Perm (Fin n)) (sylowOrder : ℕ) (d : Data) :
    Bool :=
  let a := mat a
  let b := mat b
  let sg := sgMat a b d
  let tab := tabK sg d
  let reps := d.classes.map (repMat a b)
  let good := goodOf d tab.length
  tableOkK B sylowOrder sg tab && classesOkK B a b d sg tab && censusOkK B a b d reps tab &&
  (List.range tab.length).all fun i =>
    decide (i = 0) || !keyEq B (tab.getD i 1 ^ p) 1 || good.getD i false

@[expose] def checkEMatK {n : ℕ} (B : List ℕ) (p : ℕ) (a b : Perm (Fin n)) (sylowOrder : ℕ) (d : DataE) :
    Bool :=
  let a := mat a
  let b := mat b
  let sg := sgMat a b d.base
  let tab := tabK sg d.base
  let reps := d.base.classes.map (repMat a b)
  let mul := parseMul d.mulS
  tableOkK B sylowOrder sg tab && classesOkK B a b d.base sg tab && censusOkK B a b d.base reps tab &&
  (List.range tab.length).all (fun i => (List.range tab.length).all fun j =>
    decide (sporKRestMulIdx mul i j < tab.length) &&
      keyEq B (tab.getD i 1 * tab.getD j 1) (tab.getD (sporKRestMulIdx mul i j) 1)) &&
  sporKRestECond tab.length p mul (goodOf d.base tab.length)

private theorem ggSporKRestKey_eval_mem {n : ℕ} (a b : Perm (Fin n)) (H : Subgroup (Perm (Fin n)))
    (ha : a ∈ H) (hb : b ∈ H) (w : List ℤ) :
    sporKRestEval [a, b] w ∈ H := by
  apply sporKRestEval_mem
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact ha
  · rw [List.mem_singleton] at hg
    rw [hg]
    exact hb

private theorem ggSporKRestKey_sg_mem {n : ℕ} (a b : Perm (Fin n)) (d : Data)
    (H : Subgroup (Perm (Fin n))) (ha : a ∈ H) (hb : b ∈ H) :
    ∀ g ∈ sg a b d, g ∈ H := by
  intro g hg
  simp only [sg, List.mem_map] at hg
  obtain ⟨w, _, rfl⟩ := hg
  exact ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse w)

private theorem ggSporKRestKey_tab_mem {n : ℕ} (a b : Perm (Fin n)) (d : Data)
    (H : Subgroup (Perm (Fin n))) (ha : a ∈ H) (hb : b ∈ H) :
    ∀ t ∈ tab a b d, t ∈ H := by
  intro t ht
  simp only [tab, List.mem_map] at ht
  obtain ⟨w, _, rfl⟩ := ht
  exact sporKRestEval_mem (sg a b d) (sporKRestParse w) H (ggSporKRestKey_sg_mem a b d H ha hb)

private theorem ggSporKRestKey_tab_getD_mem {n : ℕ} (a b : Perm (Fin n)) (d : Data)
    (H : Subgroup (Perm (Fin n))) (ha : a ∈ H) (hb : b ∈ H) (i : ℕ) :
    (tab a b d).getD i 1 ∈ H := by
  by_cases hi : i < (tab a b d).length
  · rw [List.getD_eq_getElem _ _ hi]
    exact ggSporKRestKey_tab_mem a b d H ha hb _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact H.one_mem

private theorem ggSporKRestKey_rep_mem {n : ℕ} (a b : Perm (Fin n))
    (H : Subgroup (Perm (Fin n))) (ha : a ∈ H) (hb : b ∈ H) (c : ClassData) :
    rep a b c ∈ H :=
  ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse c.x)

private theorem ggSporKRestKey_letters_mem {n : ℕ} (a b : Perm (Fin n)) (d : Data)
    (H : Subgroup (Perm (Fin n))) (ha : a ∈ H) (hb : b ∈ H) (c : ClassData) :
    ∀ g ∈ letters a b d c, g ∈ H := by
  intro g hg
  rw [letters, List.mem_append] at hg
  rcases hg with hg | hg
  · exact ggSporKRestKey_sg_mem a b d H ha hb g hg
  · rw [List.mem_flatMap] at hg
    obtain ⟨e, _, hg⟩ := hg
    rw [List.mem_map] at hg
    obtain ⟨w, _, rfl⟩ := hg
    exact ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse w)

private theorem ggSporKRestKey_rep_getD {n : ℕ} (a b : Perm (Fin n)) (d : Data) (i : ℕ)
    (hi : i < d.classes.length) :
    (d.classes.map (repMat a b)).getD i 1 = rep a b (d.classes.getD i ⟨"", [], "", ""⟩) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getD_eq_getElem _ _ hi, repMat_eq]

private theorem ggSporKRestKey_tabK {n : ℕ} (a b : Perm (Fin n)) (d : Data) :
    tabK (sg a b d) d = tab a b d := rfl

private theorem ggSporKRestKey_lettersK {n : ℕ} (a b : Perm (Fin n)) (d : Data) (c : ClassData) :
    lettersK (sg a b d) a b c = letters a b d c := by
  have h1 : lettersK (sg a b d) a b c = lettersMat a b d c := by
    simp only [lettersMat, lettersK, sgMat_eq]
  rw [h1, lettersMat_eq]

theorem checkMatK_sound {n : ℕ} {B : List ℕ} {a b : Perm (Fin n)} {sylowOrder : ℕ} {d : Data}
    (hB : IsBase B (Subgroup.closure ({a, b} : Set (Perm (Fin n)))))
    (h : checkMatK B a b sylowOrder d = true) : spec a b sylowOrder d := by
  let H : Subgroup (Perm (Fin n)) := Subgroup.closure ({a, b} : Set (Perm (Fin n)))
  have ha : a ∈ H := Subgroup.subset_closure (by simp)
  have hb : b ∈ H := Subgroup.subset_closure (by simp)
  unfold checkMatK at h
  dsimp only at h
  simp only [mat_eq] at h
  rw [sgMat_eq, ggSporKRestKey_tabK] at h
  simp only [tableOkK, classesOkK, censusOkK, ggSporKRestKey_lettersK, repMat_eq, keyEq,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, List.contains_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlen, hnodup_keys⟩, hkey0⟩, hmem1⟩, hcl⟩, hclasses⟩, hcensus⟩, hcov⟩ := h
  unfold spec
  refine ⟨hlen, List.Nodup.of_map (keyOf B) hnodup_keys, ?_, ?_, ?_, ?_⟩
  · obtain ⟨t, ht, hkey⟩ := List.mem_map.mp hmem1
    have ht1 : t = 1 := eq_of_keyOf_eq hB (ggSporKRestKey_tab_mem a b d H ha hb t ht) H.one_mem hkey
    rw [ht1] at ht
    exact ht
  · intro t ht g hg
    obtain ⟨h1, h2⟩ := hcl t ht g hg
    constructor
    · obtain ⟨t', ht', hkey⟩ := List.mem_map.mp h1
      have hmem : t * g ∈ H :=
        H.mul_mem (ggSporKRestKey_tab_mem a b d H ha hb t ht) (ggSporKRestKey_sg_mem a b d H ha hb g hg)
      have heq : t' = t * g :=
        eq_of_keyOf_eq hB (ggSporKRestKey_tab_mem a b d H ha hb t' ht') hmem hkey
      rw [heq] at ht'
      exact ht'
    · obtain ⟨t', ht', hkey⟩ := List.mem_map.mp h2
      have hmem : t * g⁻¹ ∈ H :=
        H.mul_mem (ggSporKRestKey_tab_mem a b d H ha hb t ht)
          (H.inv_mem (ggSporKRestKey_sg_mem a b d H ha hb g hg))
      have heq : t' = t * g⁻¹ :=
        eq_of_keyOf_eq hB (ggSporKRestKey_tab_mem a b d H ha hb t' ht') hmem hkey
      rw [heq] at ht'
      exact ht'
  · intro c hc
    obtain ⟨⟨hent, hwa⟩, hwb⟩ := hclasses c hc
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨⟨hidx, hkey⟩, hzs⟩ := hent e he
      refine ⟨hidx, ?_, ?_⟩
      · have hL : (sporKRestEval [a, b] (sporKRestParse e.h))⁻¹ * rep a b c *
            sporKRestEval [a, b] (sporKRestParse e.h) ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse e.h)))
            (ggSporKRestKey_rep_mem a b H ha hb c))
            (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse e.h))
        exact eq_of_keyOf_eq hB hL (ggSporKRestKey_tab_getD_mem a b d H ha hb e.idx) hkey
      · intro zw hzw
        have hL : sporKRestEval [a, b] (sporKRestParse zw) * (tab a b d).getD e.idx 1 ∈ H :=
          H.mul_mem (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse zw))
            (ggSporKRestKey_tab_getD_mem a b d H ha hb e.idx)
        exact eq_of_keyOf_eq hB hL (H.mul_mem (ggSporKRestKey_tab_getD_mem a b d H ha hb e.idx)
          (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse zw))) (hzs zw hzw)
    · have hL : sporKRestEval (letters a b d c) (sporKRestParse c.wa) ∈ H :=
        sporKRestEval_mem (letters a b d c) (sporKRestParse c.wa) H
          (ggSporKRestKey_letters_mem a b d H ha hb c)
      exact eq_of_keyOf_eq hB hL ha hwa
    · have hL : sporKRestEval (letters a b d c) (sporKRestParse c.wb) ∈ H :=
        sporKRestEval_mem (letters a b d c) (sporKRestParse c.wb) H
          (ggSporKRestKey_letters_mem a b d H ha hb c)
      exact eq_of_keyOf_eq hB hL hb hwb
  · intro t ht hne
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp ht
    have hgetDi : (tab a b d).getD i 1 = t := by
      rw [List.getD_eq_getElem (tab a b d) 1 hi]
      exact hget
    have h0eq : (tab a b d).getD 0 1 = 1 :=
      eq_of_keyOf_eq hB (ggSporKRestKey_tab_getD_mem a b d H ha hb 0) H.one_mem hkey0
    have hi0 : i ≠ 0 := by
      intro h0
      apply hne
      rw [← hgetDi, h0]
      exact h0eq
    have hgood : (goodOf d (tab a b d).length).getD i false = true := by
      rcases hcov i hi with h0 | h1
      · exact absurd h0 hi0
      · exact h1
    simp only [goodOf] at hgood
    rw [List.getD_eq_getElem _ false (by simpa using hi), List.getElem_map,
      List.getElem_range] at hgood
    obtain ⟨e, he, het⟩ := List.any_eq_true.mp hgood
    have heti : e.t = i := beq_iff_eq.mp het
    obtain ⟨⟨⟨hcls, _htlt⟩, _hne0⟩, hconj⟩ := hcensus e he
    refine ⟨e, he, hcls, ?_, ?_⟩
    · rw [heti]
      exact hgetDi
    · have hL : (sporKRestEval [a, b] (sporKRestParse e.g))⁻¹ *
          rep a b (d.classes.getD e.cls ⟨"", [], "", ""⟩) *
          sporKRestEval [a, b] (sporKRestParse e.g) ∈ H :=
        H.mul_mem (H.mul_mem (H.inv_mem (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse e.g)))
          (ggSporKRestKey_rep_mem a b H ha hb _))
          (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse e.g))
      have hkey' : keyOf B ((sporKRestEval [a, b] (sporKRestParse e.g))⁻¹ *
          rep a b (d.classes.getD e.cls ⟨"", [], "", ""⟩) *
          sporKRestEval [a, b] (sporKRestParse e.g)) = keyOf B t := by
        rw [ggSporKRestKey_rep_getD a b d e.cls hcls, heti, hgetDi] at hconj
        exact hconj
      exact eq_of_keyOf_eq hB hL (ggSporKRestKey_tab_mem a b d H ha hb t ht) hkey'

theorem checkPowMatK_sound {n : ℕ} {B : List ℕ} {p : ℕ} {a b : Perm (Fin n)} {sylowOrder : ℕ} {d : Data}
    (hB : IsBase B (Subgroup.closure ({a, b} : Set (Perm (Fin n)))))
    (h : checkPowMatK B p a b sylowOrder d = true) : specPow p a b sylowOrder d := by
  let H : Subgroup (Perm (Fin n)) := Subgroup.closure ({a, b} : Set (Perm (Fin n)))
  have ha : a ∈ H := Subgroup.subset_closure (by simp)
  have hb : b ∈ H := Subgroup.subset_closure (by simp)
  unfold checkPowMatK at h
  dsimp only at h
  simp only [mat_eq] at h
  rw [sgMat_eq, ggSporKRestKey_tabK] at h
  simp only [tableOkK, classesOkK, censusOkK, ggSporKRestKey_lettersK, repMat_eq, keyEq,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, List.contains_iff, Bool.not_eq_true_eq_eq_false,
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlen, hnodup_keys⟩, hkey0⟩, hmem1⟩, hcl⟩, hclasses⟩, hcensus⟩, hcov⟩ := h
  unfold specPow
  refine ⟨hlen, List.Nodup.of_map (keyOf B) hnodup_keys, ?_, ?_, ?_, ?_⟩
  · obtain ⟨t, ht, hkey⟩ := List.mem_map.mp hmem1
    have ht1 : t = 1 := eq_of_keyOf_eq hB (ggSporKRestKey_tab_mem a b d H ha hb t ht) H.one_mem hkey
    rw [ht1] at ht
    exact ht
  · intro t ht g hg
    obtain ⟨h1, h2⟩ := hcl t ht g hg
    constructor
    · obtain ⟨t', ht', hkey⟩ := List.mem_map.mp h1
      have hmem : t * g ∈ H :=
        H.mul_mem (ggSporKRestKey_tab_mem a b d H ha hb t ht) (ggSporKRestKey_sg_mem a b d H ha hb g hg)
      have heq : t' = t * g :=
        eq_of_keyOf_eq hB (ggSporKRestKey_tab_mem a b d H ha hb t' ht') hmem hkey
      rw [heq] at ht'
      exact ht'
    · obtain ⟨t', ht', hkey⟩ := List.mem_map.mp h2
      have hmem : t * g⁻¹ ∈ H :=
        H.mul_mem (ggSporKRestKey_tab_mem a b d H ha hb t ht)
          (H.inv_mem (ggSporKRestKey_sg_mem a b d H ha hb g hg))
      have heq : t' = t * g⁻¹ :=
        eq_of_keyOf_eq hB (ggSporKRestKey_tab_mem a b d H ha hb t' ht') hmem hkey
      rw [heq] at ht'
      exact ht'
  · intro c hc
    obtain ⟨⟨hent, hwa⟩, hwb⟩ := hclasses c hc
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨⟨hidx, hkey⟩, hzs⟩ := hent e he
      refine ⟨hidx, ?_, ?_⟩
      · have hL : (sporKRestEval [a, b] (sporKRestParse e.h))⁻¹ * rep a b c *
            sporKRestEval [a, b] (sporKRestParse e.h) ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse e.h)))
            (ggSporKRestKey_rep_mem a b H ha hb c))
            (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse e.h))
        exact eq_of_keyOf_eq hB hL (ggSporKRestKey_tab_getD_mem a b d H ha hb e.idx) hkey
      · intro zw hzw
        have hL : sporKRestEval [a, b] (sporKRestParse zw) * (tab a b d).getD e.idx 1 ∈ H :=
          H.mul_mem (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse zw))
            (ggSporKRestKey_tab_getD_mem a b d H ha hb e.idx)
        exact eq_of_keyOf_eq hB hL (H.mul_mem (ggSporKRestKey_tab_getD_mem a b d H ha hb e.idx)
          (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse zw))) (hzs zw hzw)
    · have hL : sporKRestEval (letters a b d c) (sporKRestParse c.wa) ∈ H :=
        sporKRestEval_mem (letters a b d c) (sporKRestParse c.wa) H
          (ggSporKRestKey_letters_mem a b d H ha hb c)
      exact eq_of_keyOf_eq hB hL ha hwa
    · have hL : sporKRestEval (letters a b d c) (sporKRestParse c.wb) ∈ H :=
        sporKRestEval_mem (letters a b d c) (sporKRestParse c.wb) H
          (ggSporKRestKey_letters_mem a b d H ha hb c)
      exact eq_of_keyOf_eq hB hL hb hwb
  · intro t ht hne hp
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp ht
    have hgetDi : (tab a b d).getD i 1 = t := by
      rw [List.getD_eq_getElem (tab a b d) 1 hi]
      exact hget
    have h0eq : (tab a b d).getD 0 1 = 1 :=
      eq_of_keyOf_eq hB (ggSporKRestKey_tab_getD_mem a b d H ha hb 0) H.one_mem hkey0
    have hi0 : i ≠ 0 := by
      intro h0
      apply hne
      rw [← hgetDi, h0]
      exact h0eq
    have hgood : (goodOf d (tab a b d).length).getD i false = true := by
      rcases hcov i hi with (h0 | hpne) | hg
      · exact absurd h0 hi0
      · exact absurd (by rw [hgetDi, hp]) hpne
      · exact hg
    simp only [goodOf] at hgood
    rw [List.getD_eq_getElem _ false (by simpa using hi), List.getElem_map,
      List.getElem_range] at hgood
    obtain ⟨e, he, het⟩ := List.any_eq_true.mp hgood
    have heti : e.t = i := beq_iff_eq.mp het
    obtain ⟨⟨⟨hcls, _htlt⟩, _hne0⟩, hconj⟩ := hcensus e he
    refine ⟨e, he, hcls, ?_, ?_⟩
    · rw [heti]
      exact hgetDi
    · have hL : (sporKRestEval [a, b] (sporKRestParse e.g))⁻¹ *
          rep a b (d.classes.getD e.cls ⟨"", [], "", ""⟩) *
          sporKRestEval [a, b] (sporKRestParse e.g) ∈ H :=
        H.mul_mem (H.mul_mem (H.inv_mem (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse e.g)))
          (ggSporKRestKey_rep_mem a b H ha hb _))
          (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse e.g))
      have hkey' : keyOf B ((sporKRestEval [a, b] (sporKRestParse e.g))⁻¹ *
          rep a b (d.classes.getD e.cls ⟨"", [], "", ""⟩) *
          sporKRestEval [a, b] (sporKRestParse e.g)) = keyOf B t := by
        rw [ggSporKRestKey_rep_getD a b d e.cls hcls, heti, hgetDi] at hconj
        exact hconj
      exact eq_of_keyOf_eq hB hL (ggSporKRestKey_tab_mem a b d H ha hb t ht) hkey'

theorem checkEMatK_sound {n : ℕ} {B : List ℕ} {p : ℕ} {a b : Perm (Fin n)} {sylowOrder : ℕ} {d : DataE}
    (hB : IsBase B (Subgroup.closure ({a, b} : Set (Perm (Fin n)))))
    (h : checkEMatK B p a b sylowOrder d = true) : specE p a b sylowOrder d := by
  let H : Subgroup (Perm (Fin n)) := Subgroup.closure ({a, b} : Set (Perm (Fin n)))
  have ha : a ∈ H := Subgroup.subset_closure (by simp)
  have hb : b ∈ H := Subgroup.subset_closure (by simp)
  unfold checkEMatK at h
  dsimp only at h
  simp only [mat_eq] at h
  rw [sgMat_eq, ggSporKRestKey_tabK] at h
  simp only [tableOkK, classesOkK, censusOkK, ggSporKRestKey_lettersK, repMat_eq, keyEq,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, List.contains_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hlen, hnodup_keys⟩, hkey0⟩, _hmem1⟩, hcl⟩, hclasses⟩, hcensus⟩, hmul⟩, hcond⟩ := h
  unfold specE
  refine ⟨hlen, List.Nodup.of_map (keyOf B) hnodup_keys, ?_, ?_, ?_, ?_, ?_, hcond⟩
  · exact eq_of_keyOf_eq hB (ggSporKRestKey_tab_getD_mem a b d.base H ha hb 0) H.one_mem hkey0
  · intro t ht g hg
    obtain ⟨h1, h2⟩ := hcl t ht g hg
    constructor
    · obtain ⟨t', ht', hkey⟩ := List.mem_map.mp h1
      have hmem : t * g ∈ H :=
        H.mul_mem (ggSporKRestKey_tab_mem a b d.base H ha hb t ht)
          (ggSporKRestKey_sg_mem a b d.base H ha hb g hg)
      have heq : t' = t * g :=
        eq_of_keyOf_eq hB (ggSporKRestKey_tab_mem a b d.base H ha hb t' ht') hmem hkey
      rw [heq] at ht'
      exact ht'
    · obtain ⟨t', ht', hkey⟩ := List.mem_map.mp h2
      have hmem : t * g⁻¹ ∈ H :=
        H.mul_mem (ggSporKRestKey_tab_mem a b d.base H ha hb t ht)
          (H.inv_mem (ggSporKRestKey_sg_mem a b d.base H ha hb g hg))
      have heq : t' = t * g⁻¹ :=
        eq_of_keyOf_eq hB (ggSporKRestKey_tab_mem a b d.base H ha hb t' ht') hmem hkey
      rw [heq] at ht'
      exact ht'
  · intro c hc
    obtain ⟨⟨hent, hwa⟩, hwb⟩ := hclasses c hc
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨⟨hidx, hkey⟩, hzs⟩ := hent e he
      refine ⟨hidx, ?_, ?_⟩
      · have hL : (sporKRestEval [a, b] (sporKRestParse e.h))⁻¹ * rep a b c *
            sporKRestEval [a, b] (sporKRestParse e.h) ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse e.h)))
            (ggSporKRestKey_rep_mem a b H ha hb c))
            (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse e.h))
        exact eq_of_keyOf_eq hB hL (ggSporKRestKey_tab_getD_mem a b d.base H ha hb e.idx) hkey
      · intro zw hzw
        have hL : sporKRestEval [a, b] (sporKRestParse zw) * (tab a b d.base).getD e.idx 1 ∈ H :=
          H.mul_mem (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse zw))
            (ggSporKRestKey_tab_getD_mem a b d.base H ha hb e.idx)
        exact eq_of_keyOf_eq hB hL (H.mul_mem (ggSporKRestKey_tab_getD_mem a b d.base H ha hb e.idx)
          (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse zw))) (hzs zw hzw)
    · have hL : sporKRestEval (letters a b d.base c) (sporKRestParse c.wa) ∈ H :=
        sporKRestEval_mem (letters a b d.base c) (sporKRestParse c.wa) H
          (ggSporKRestKey_letters_mem a b d.base H ha hb c)
      exact eq_of_keyOf_eq hB hL ha hwa
    · have hL : sporKRestEval (letters a b d.base c) (sporKRestParse c.wb) ∈ H :=
        sporKRestEval_mem (letters a b d.base c) (sporKRestParse c.wb) H
          (ggSporKRestKey_letters_mem a b d.base H ha hb c)
      exact eq_of_keyOf_eq hB hL hb hwb
  · intro e he
    obtain ⟨⟨⟨hcls, htlt⟩, hne0⟩, hconj⟩ := hcensus e he
    refine ⟨hcls, htlt, hne0, ?_⟩
    have hL : (sporKRestEval [a, b] (sporKRestParse e.g))⁻¹ *
        rep a b (d.base.classes.getD e.cls ⟨"", [], "", ""⟩) *
        sporKRestEval [a, b] (sporKRestParse e.g) ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse e.g)))
        (ggSporKRestKey_rep_mem a b H ha hb _))
        (ggSporKRestKey_eval_mem a b H ha hb (sporKRestParse e.g))
    have hkey : keyOf B ((sporKRestEval [a, b] (sporKRestParse e.g))⁻¹ *
        rep a b (d.base.classes.getD e.cls ⟨"", [], "", ""⟩) *
        sporKRestEval [a, b] (sporKRestParse e.g)) = keyOf B ((tab a b d.base).getD e.t 1) := by
      rw [ggSporKRestKey_rep_getD a b d.base e.cls hcls] at hconj
      exact hconj
    exact eq_of_keyOf_eq hB hL (ggSporKRestKey_tab_getD_mem a b d.base H ha hb e.t) hkey
  · intro i hi j hj
    obtain ⟨hlt, hkey⟩ := hmul i hi j hj
    refine ⟨hlt, ?_⟩
    have hL : (tab a b d.base).getD i 1 * (tab a b d.base).getD j 1 ∈ H :=
      H.mul_mem (ggSporKRestKey_tab_getD_mem a b d.base H ha hb i)
        (ggSporKRestKey_tab_getD_mem a b d.base H ha hb j)
    exact eq_of_keyOf_eq hB hL
      (ggSporKRestKey_tab_getD_mem a b d.base H ha hb (sporKRestMulIdx (parseMul d.mulS) i j)) hkey

end CFSG.StandardType.SporadicShape.PermCover
