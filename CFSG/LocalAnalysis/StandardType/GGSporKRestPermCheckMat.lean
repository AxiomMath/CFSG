module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestMat
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheckPow
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheckE
public import Mathlib.Data.List.GetD

public section

namespace CFSG.StandardType.SporadicShape.PermCover

open Equiv

@[expose] def sgMat {n : ℕ} (a b : Perm (Fin n)) (d : Data) : List (Perm (Fin n)) :=
  d.sgW.map fun w => mat (sporKRestEval [a, b] (sporKRestParse w))

@[expose] def tabMat {n : ℕ} (a b : Perm (Fin n)) (d : Data) : List (Perm (Fin n)) :=
  d.tabW.map fun w => mat (sporKRestEval (sgMat a b d) (sporKRestParse w))

@[expose] def repMat {n : ℕ} (a b : Perm (Fin n)) (c : ClassData) : Perm (Fin n) :=
  mat (sporKRestEval [a, b] (sporKRestParse c.x))

@[expose] def lettersMat {n : ℕ} (a b : Perm (Fin n)) (d : Data) (c : ClassData) : List (Perm (Fin n)) :=
  sgMat a b d ++ c.ent.flatMap fun e => e.zs.map fun w => mat (sporKRestEval [a, b] (sporKRestParse w))

theorem sgMat_eq {n : ℕ} (a b : Perm (Fin n)) (d : Data) : sgMat a b d = sg a b d := by
  simp only [sgMat, sg]
  apply List.map_congr_left
  intro w _
  exact mat_eq _

theorem tabMat_eq {n : ℕ} (a b : Perm (Fin n)) (d : Data) : tabMat a b d = tab a b d := by
  simp only [tabMat, tab, sgMat_eq]
  apply List.map_congr_left
  intro w _
  exact mat_eq _

theorem repMat_eq {n : ℕ} (a b : Perm (Fin n)) (c : ClassData) : repMat a b c = rep a b c := by
  simp only [repMat, rep]
  exact mat_eq _

theorem lettersMat_eq {n : ℕ} (a b : Perm (Fin n)) (d : Data) (c : ClassData) :
    lettersMat a b d c = letters a b d c := by
  simp only [lettersMat, letters, sgMat_eq]
  congr 1
  apply List.flatMap_congr
  intro e _
  apply List.map_congr_left
  intro w _
  exact mat_eq _

@[expose] def tableOkMat {n : ℕ} (sylowOrder : ℕ) (sg tab : List (Perm (Fin n))) : Bool :=
  decide (tab.length = sylowOrder) && permNodup tab && permEq (tab.getD 0 1) 1 &&
  permMem (1 : Perm (Fin n)) tab &&
  tab.all (fun t => sg.all fun g => permMem (t * g) tab && permMem (t * g⁻¹) tab)

@[expose] def classesOkMat {n : ℕ} (a b : Perm (Fin n)) (d : Data) (tab : List (Perm (Fin n))) : Bool :=
  d.classes.all (fun c =>
    c.ent.all (fun e => decide (e.idx < tab.length) &&
      permEq ((sporKRestEval [a, b] (sporKRestParse e.h))⁻¹ * repMat a b c *
        sporKRestEval [a, b] (sporKRestParse e.h)) (tab.getD e.idx 1) &&
      e.zs.all fun zw => permEq (sporKRestEval [a, b] (sporKRestParse zw) * tab.getD e.idx 1)
        (tab.getD e.idx 1 * sporKRestEval [a, b] (sporKRestParse zw))) &&
    permEq (sporKRestEval (lettersMat a b d c) (sporKRestParse c.wa)) a &&
    permEq (sporKRestEval (lettersMat a b d c) (sporKRestParse c.wb)) b)

@[expose] def censusOkMat {n : ℕ} (a b : Perm (Fin n)) (d : Data) (tab : List (Perm (Fin n))) : Bool :=
  d.census.all (fun e => decide (e.cls < d.classes.length) && decide (e.t < tab.length) &&
    decide (e.t ≠ 0) &&
    permEq ((sporKRestEval [a, b] (sporKRestParse e.g))⁻¹ *
      repMat a b (d.classes.getD e.cls ⟨"", [], "", ""⟩) * sporKRestEval [a, b] (sporKRestParse e.g))
        (tab.getD e.t 1))

@[expose] def checkMat {n : ℕ} (a b : Perm (Fin n)) (sylowOrder : ℕ) (d : Data) : Bool :=
  let a := mat a
  let b := mat b
  let sg := sgMat a b d
  let tab := tabMat a b d
  let good := goodOf d tab.length
  tableOkMat sylowOrder sg tab && classesOkMat a b d tab && censusOkMat a b d tab &&
  (List.range tab.length).all fun i => decide (i = 0) || good.getD i false

@[expose] def checkPowMat {n : ℕ} (p : ℕ) (a b : Perm (Fin n)) (sylowOrder : ℕ) (d : Data) : Bool :=
  let a := mat a
  let b := mat b
  let sg := sgMat a b d
  let tab := tabMat a b d
  let good := goodOf d tab.length
  tableOkMat sylowOrder sg tab && classesOkMat a b d tab && censusOkMat a b d tab &&
  (List.range tab.length).all fun i =>
    decide (i = 0) || !permEq (tab.getD i 1 ^ p) 1 || good.getD i false

@[expose] def checkEMat {n : ℕ} (p : ℕ) (a b : Perm (Fin n)) (sylowOrder : ℕ) (d : DataE) : Bool :=
  let a := mat a
  let b := mat b
  let sg := sgMat a b d.base
  let tab := tabMat a b d.base
  let mul := parseMul d.mulS
  tableOkMat sylowOrder sg tab && classesOkMat a b d.base tab && censusOkMat a b d.base tab &&
  (List.range tab.length).all (fun i => (List.range tab.length).all fun j =>
    decide (sporKRestMulIdx mul i j < tab.length) &&
      permEq (tab.getD i 1 * tab.getD j 1) (tab.getD (sporKRestMulIdx mul i j) 1)) &&
  sporKRestECond tab.length p mul (goodOf d.base tab.length)

theorem checkMat_sound {n : ℕ} {a b : Perm (Fin n)} {sylowOrder : ℕ} {d : Data}
    (h : checkMat a b sylowOrder d = true) : spec a b sylowOrder d := by
  unfold checkMat at h
  dsimp only at h
  simp only [mat_eq] at h
  rw [sgMat_eq, tabMat_eq] at h
  simp only [tableOkMat, classesOkMat, censusOkMat, repMat_eq, lettersMat_eq,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, permEq_iff, permMem_iff, permNodup_iff,
    Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff] at h
  obtain ⟨⟨⟨⟨hlen, hnodup⟩, hgetD⟩, hmem⟩, hall⟩ := h.1.1.1
  have hclasses := h.1.1.2
  have hcensus := h.1.2
  have hcov := h.2
  unfold spec
  refine ⟨hlen, hnodup, hmem, hall, ?_, ?_⟩
  · intro c hc
    obtain ⟨⟨hent, hwa⟩, hwb⟩ := hclasses c hc
    refine ⟨?_, hwa, hwb⟩
    intro e he
    obtain ⟨⟨hidx, hh⟩, hzs⟩ := hent e he
    exact ⟨hidx, hh, hzs⟩
  · intro t ht hne
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp ht
    have hgetDi : (tab a b d).getD i 1 = t := by
      rw [List.getD_eq_getElem (tab a b d) 1 hi]
      exact hget
    have hi0 : i ≠ 0 := by
      intro h0
      apply hne
      rw [← hgetDi, h0]
      exact hgetD
    have hgood : (goodOf d (tab a b d).length).getD i false = true := by
      rcases hcov i hi with h0 | h1
      · exact absurd h0 hi0
      · exact h1
    simp only [goodOf] at hgood
    rw [List.getD_eq_getElem _ false (by simpa using hi), List.getElem_map,
      List.getElem_range] at hgood
    obtain ⟨e, he, het⟩ := List.any_eq_true.mp hgood
    have heti : e.t = i := beq_iff_eq.mp het
    obtain ⟨⟨⟨hcls, _hte⟩, _hne0⟩, hconj⟩ := hcensus e he
    refine ⟨e, he, hcls, ?_, ?_⟩
    · rw [heti]
      exact hgetDi
    · rw [heti, hgetDi] at hconj
      exact hconj

theorem checkPowMat_sound {n : ℕ} {p : ℕ} {a b : Perm (Fin n)} {sylowOrder : ℕ} {d : Data}
    (h : checkPowMat p a b sylowOrder d = true) : specPow p a b sylowOrder d := by
  unfold checkPowMat at h
  dsimp only at h
  simp only [mat_eq] at h
  rw [sgMat_eq, tabMat_eq] at h
  simp only [tableOkMat, classesOkMat, censusOkMat, repMat_eq, lettersMat_eq,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, permEq_iff, permMem_iff, permNodup_iff,
    Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff] at h
  obtain ⟨⟨⟨⟨hlen, hnodup⟩, hgetD⟩, hmem⟩, hall⟩ := h.1.1.1
  have hclasses := h.1.1.2
  have hcensus := h.1.2
  have hcov := h.2
  unfold specPow
  refine ⟨hlen, hnodup, hmem, hall, ?_, ?_⟩
  · intro c hc
    obtain ⟨⟨hent, hwa⟩, hwb⟩ := hclasses c hc
    refine ⟨?_, hwa, hwb⟩
    intro e he
    obtain ⟨⟨hidx, hh⟩, hzs⟩ := hent e he
    exact ⟨hidx, hh, hzs⟩
  · intro t ht hne hp
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp ht
    have hgetDi : (tab a b d).getD i 1 = t := by
      rw [List.getD_eq_getElem (tab a b d) 1 hi]
      exact hget
    have hi0 : i ≠ 0 := by
      intro h0
      apply hne
      rw [← hgetDi, h0]
      exact hgetD
    have hgood : (goodOf d (tab a b d).length).getD i false = true := by
      rcases hcov i hi with (h0 | hpne) | hg
      · exact absurd h0 hi0
      · exact absurd ((permEq_iff ((tab a b d).getD i 1 ^ p) 1).mpr (by rw [hgetDi]; exact hp)) hpne
      · exact hg
    simp only [goodOf] at hgood
    rw [List.getD_eq_getElem _ false (by simpa using hi), List.getElem_map,
      List.getElem_range] at hgood
    obtain ⟨e, he, het⟩ := List.any_eq_true.mp hgood
    have heti : e.t = i := beq_iff_eq.mp het
    obtain ⟨⟨⟨hcls, _hte⟩, _hne0⟩, hconj⟩ := hcensus e he
    refine ⟨e, he, hcls, ?_, ?_⟩
    · rw [heti]
      exact hgetDi
    · rw [heti, hgetDi] at hconj
      exact hconj

theorem checkEMat_sound {n : ℕ} {p : ℕ} {a b : Perm (Fin n)} {sylowOrder : ℕ} {d : DataE}
    (h : checkEMat p a b sylowOrder d = true) : specE p a b sylowOrder d := by
  unfold checkEMat at h
  dsimp only at h
  simp only [mat_eq] at h
  rw [sgMat_eq, tabMat_eq] at h
  simp only [tableOkMat, classesOkMat, censusOkMat, repMat_eq, lettersMat_eq,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    permEq_iff, permMem_iff, permNodup_iff] at h
  obtain ⟨⟨⟨⟨hlen, hnodup⟩, hgetD⟩, hmem⟩, hall⟩ := h.1.1.1.1
  have hclasses := h.1.1.1.2
  have hcensus := h.1.1.2
  have hmul := h.1.2
  have hcond := h.2
  unfold specE
  refine ⟨hlen, hnodup, hgetD, hall, ?_, ?_, ?_, hcond⟩
  · intro c hc
    obtain ⟨⟨hent, hwa⟩, hwb⟩ := hclasses c hc
    refine ⟨?_, hwa, hwb⟩
    intro e he
    obtain ⟨⟨hidx, hh⟩, hzs⟩ := hent e he
    exact ⟨hidx, hh, hzs⟩
  · intro e he
    obtain ⟨⟨⟨hcls, ht⟩, hne⟩, hconj⟩ := hcensus e he
    exact ⟨hcls, ht, hne, hconj⟩
  · intro i hi j hj
    exact hmul i hi j hj

theorem check_of_spec {n : ℕ} {a b : Perm (Fin n)} {sylowOrder : ℕ} {d : Data}
    (h : spec a b sylowOrder d) : check a b sylowOrder d = true := by
  unfold spec at h
  obtain ⟨hlen, hnodup, hmem, hcl, hclasses, hcensus⟩ := h
  unfold check
  dsimp only
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨hlen, hnodup⟩, hmem⟩, ?_⟩, ?_⟩, ?_⟩
  · intro t ht g hg
    exact hcl t ht g hg
  · intro c hc
    obtain ⟨hent, hwa, hwb⟩ := hclasses c hc
    refine ⟨⟨?_, hwa⟩, hwb⟩
    intro e he
    obtain ⟨hidx, hh, hzs⟩ := hent e he
    exact ⟨⟨hidx, hh⟩, hzs⟩
  · intro t ht
    by_cases ht1 : t = 1
    · exact Or.inl ht1
    · obtain ⟨e, he, hcls, hget, hconj⟩ := hcensus t ht ht1
      exact Or.inr ⟨e, he, ⟨⟨hcls, hget⟩, hconj⟩⟩

theorem checkPow_of_spec {n : ℕ} {p : ℕ} {a b : Perm (Fin n)} {sylowOrder : ℕ} {d : Data}
    (h : specPow p a b sylowOrder d) : checkPow p a b sylowOrder d = true := by
  unfold specPow at h
  obtain ⟨hlen, hnodup, hmem, hcl, hclasses, hcensus⟩ := h
  unfold checkPow
  dsimp only
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨hlen, hnodup⟩, hmem⟩, ?_⟩, ?_⟩, ?_⟩
  · intro t ht g hg
    exact hcl t ht g hg
  · intro c hc
    obtain ⟨hent, hwa, hwb⟩ := hclasses c hc
    refine ⟨⟨?_, hwa⟩, hwb⟩
    intro e he
    obtain ⟨hidx, hh, hzs⟩ := hent e he
    exact ⟨⟨hidx, hh⟩, hzs⟩
  · intro t ht
    by_cases ht1 : t = 1
    · exact Or.inl (Or.inl ht1)
    · by_cases hp : t ^ p = 1
      · obtain ⟨e, he, hcls, hget, hconj⟩ := hcensus t ht ht1 hp
        exact Or.inr ⟨e, he, ⟨⟨hcls, hget⟩, hconj⟩⟩
      · exact Or.inl (Or.inr hp)

theorem checkE_of_spec {n : ℕ} {p : ℕ} {a b : Perm (Fin n)} {sylowOrder : ℕ} {d : DataE}
    (h : specE p a b sylowOrder d) : checkE p a b sylowOrder d = true := by
  unfold specE at h
  obtain ⟨hlen, hnodup, hgetD, hcl, hclasses, hcensus, hmul, hcond⟩ := h
  unfold checkE
  dsimp only
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨hlen, hnodup⟩, hgetD⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hcond⟩
  · intro t ht g hg
    exact hcl t ht g hg
  · intro c hc
    obtain ⟨hent, hwa, hwb⟩ := hclasses c hc
    refine ⟨⟨?_, hwa⟩, hwb⟩
    intro e he
    obtain ⟨hidx, hh, hzs⟩ := hent e he
    exact ⟨⟨hidx, hh⟩, hzs⟩
  · intro e he
    obtain ⟨hcls, ht, hne, hconj⟩ := hcensus e he
    exact ⟨⟨⟨hcls, ht⟩, hne⟩, hconj⟩
  · intro i hi j hj
    exact hmul i hi j hj

end CFSG.StandardType.SporadicShape.PermCover
