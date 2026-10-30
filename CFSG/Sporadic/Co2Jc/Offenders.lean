module

public import CFSG.Sporadic.Co2Jc.Omega
public import CFSG.Sporadic.Co2Jc.Linear
public import Certificates.Certificate719030

public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith Subgroup
open scoped IsMulCommutative

theorem mem_checks_true {b : Bool} (hb : b ∈ Native.checks) : b = true := by
  have h : Native.checks.all id = true := by
    rw [← Native.offendersOK]
    exact Certificates.certificate719030
  exact List.all_eq_true.mp h b hb

theorem lenOK_true : Native.lenOK = true := mem_checks_true (by simp [Native.checks])
theorem nodupOK_true : Native.nodupOK = true := mem_checks_true (by simp [Native.checks])
theorem tabOK_true : Native.tabOK = true := mem_checks_true (by simp [Native.checks])
theorem wordsOK_true : Native.wordsOK = true := mem_checks_true (by simp [Native.checks])
theorem parentOK_true : Native.parentOK = true := mem_checks_true (by simp [Native.checks])
theorem closedOK_true : Native.closedOK = true := mem_checks_true (by simp [Native.checks])
theorem mulIdxOK_true : Native.mulIdxOK = true := mem_checks_true (by simp [Native.checks])
theorem subsOK_true : Native.subsOK = true := mem_checks_true (by simp [Native.checks])
theorem involOK_true : Native.involOK = true := mem_checks_true (by simp [Native.checks])
theorem stepOK_true : Native.stepOK = true := mem_checks_true (by simp [Native.checks])
theorem boundOK_true : Native.boundOK = true := mem_checks_true (by simp [Native.checks])

theorem tabs_length : Native.tabs.length = 256 := beq_iff_eq.mp lenOK_true

theorem nodup_spec {i j : ℕ} (hi : i < 256) (hj : j < 256) (hij : i ≠ j) :
    Native.tabs.getD i [] ≠ Native.tabs.getD j [] := by
  have h := nodupOK_true
  simp only [Native.nodupOK, List.all_eq_true, List.mem_range] at h
  have h2 := h i hi j hj
  rw [show (i == j) = false from by simpa using hij] at h2
  simpa using h2

theorem tab_mem_spec {l : List ℕ} (hl : l ∈ Native.tabs) :
    l.length = 10 ∧ ∀ c ∈ l, c < 1024 := by
  have h := tabOK_true
  simp only [Native.tabOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h l hl

theorem words_lt3 : ∀ w ∈ Data.sylW, ∀ k ∈ w, k < 3 := by
  have h := wordsOK_true
  simp only [Native.wordsOK, List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem tabs_zero : Native.tabs.getD 0 [] = Native.idTab := by
  have h := parentOK_true
  simp only [Native.parentOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem parent_spec {i : ℕ} (hi : i < Native.tabs.length) (hi0 : i ≠ 0) :
    ∃ p < i, ∃ k < 4,
      Native.tabs.getD i [] = Native.compL (Native.gens.getD k []) (Native.tabs.getD p []) := by
  have h := parentOK_true
  simp only [Native.parentOK, Bool.and_eq_true, beq_iff_eq] at h
  have h2 := (List.all_eq_true.mp h.2) i (List.mem_range.mpr hi)
  rw [show (i == 0) = false from by simpa using hi0] at h2
  rw [Bool.false_or] at h2
  rw [List.any_eq_true] at h2
  obtain ⟨p, hp, hk⟩ := h2
  rw [List.mem_range] at hp
  rw [List.any_eq_true] at hk
  obtain ⟨k, hk, hpk⟩ := hk
  rw [List.mem_range] at hk
  exact ⟨p, hp, k, hk, beq_iff_eq.mp hpk⟩

theorem gens_length : Native.gens.length = 4 := by
  simp [Native.gens]

theorem tab_getD_idxOf {l : List ℕ} (hl : l ∈ Native.tabs) :
    Native.tabs.getD (Native.tabs.idxOf l) [] = l := by
  have hlt : Native.tabs.idxOf l < Native.tabs.length := List.idxOf_lt_length_iff.mpr hl
  rw [List.getD_eq_getElem (l := Native.tabs) (n := Native.tabs.idxOf l) (d := []) hlt]
  exact List.getElem_idxOf hlt

theorem closed_spec {i k : ℕ} (hi : i < 256) (hk : k < 4) :
    Native.compL (Native.gens.getD k []) (Native.tabs.getD i []) ∈ Native.tabs := by
  have h := closedOK_true
  simp only [Native.closedOK, List.all_eq_true, List.mem_range, List.contains_iff_mem] at h
  have hk' : k < Native.gens.length := by rw [gens_length]; exact hk
  exact h i hi k hk'

theorem closed_spec_mem {l : List ℕ} (hl : l ∈ Native.tabs) {k : ℕ} (hk : k < 4) :
    Native.compL (Native.gens.getD k []) l ∈ Native.tabs := by
  have hlt : Native.tabs.idxOf l < 256 := by
    rw [← tabs_length]; exact List.idxOf_lt_length_iff.mpr hl
  rw [← tab_getD_idxOf hl]
  exact closed_spec hlt hk

theorem mulIdx_spec {s i : ℕ} (hs : s < 256) (hi : i < 256) :
    Native.mulIdxC s i < 256 ∧
      Native.tabs.getD (Native.mulIdxC s i) [] =
        Native.compL (Native.tabs.getD s []) (Native.tabs.getD i []) := by
  have h := mulIdxOK_true
  simp only [Native.mulIdxOK, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  exact h s hs i hi

theorem subs_mem_spec {l : List ℕ} (hl : l ∈ Native.subs) :
    (0 ∈ l ∧ (∀ i ∈ l, i < 256)) ∧ l.Nodup := by
  have h := subsOK_true
  simp only [Native.subsOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.contains_iff_mem] at h
  exact h.2 l hl

theorem invol_spec {s : ℕ} (hs : s < 256) (hs0 : s ≠ 0)
    (hne : Native.tabs.getD s [] ≠ Native.idTab)
    (hinv : Native.compL (Native.tabs.getD s []) (Native.tabs.getD s []) = Native.idTab) :
    Native.pairOf s ∈ Native.subs := by
  have h := involOK_true
  simp only [Native.involOK, List.all_eq_true, List.mem_range] at h
  have h2 := h s hs
  rw [show (s == 0) = false from by simpa using hs0] at h2
  simp only [Bool.false_or] at h2
  rw [show (Native.tabs.getD s [] == Native.idTab) = false from by simpa using hne] at h2
  simp only [Bool.false_or] at h2
  rw [show (Native.compL (Native.tabs.getD s []) (Native.tabs.getD s []) != Native.idTab) =
    false from by simpa using hinv] at h2
  simpa using h2

theorem step_spec {l : List ℕ} (hl : l ∈ Native.subs) {s : ℕ} (hs : s < 256)
    (hsnot : s ∉ l) (hne : Native.tabs.getD s [] ≠ Native.idTab)
    (hinv : Native.compL (Native.tabs.getD s []) (Native.tabs.getD s []) = Native.idTab)
    (hcomm : Native.commutesAll s l = true) : Native.stepL l s ∈ Native.subs := by
  have h := stepOK_true
  simp only [Native.stepOK, List.all_eq_true, List.mem_range] at h
  have h2 := h l hl s hs
  rw [show l.contains s = false from by
    rw [List.contains_eq_mem]
    simpa using hsnot] at h2
  simp only [Bool.false_or] at h2
  rw [show (Native.tabs.getD s [] == Native.idTab) = false from by simpa using hne] at h2
  simp only [Bool.false_or] at h2
  rw [show (Native.compL (Native.tabs.getD s []) (Native.tabs.getD s []) != Native.idTab) =
    false from by simpa using hinv] at h2
  simp only [Bool.false_or] at h2
  rw [show (!Native.commutesAll s l) = false from by simpa using hcomm] at h2
  simpa using h2

theorem bound_spec {l : List ℕ} (hl : l ∈ Native.subs) :
    l.length * Native.fixCount l ≤ 512 := by
  have h := boundOK_true
  simp only [Native.boundOK, List.all_eq_true, decide_eq_true_eq] at h
  exact h l hl

private theorem foldr_if_xor (l : List ℕ) (c : ℕ → ℕ) (x : ℕ) :
    l.foldr (fun i acc => if x.testBit i then c i ^^^ acc else acc) 0 =
      l.foldr (fun i acc => (if x.testBit i then c i else 0) ^^^ acc) 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    split <;> simp

theorem colAct_eq_xorList (c : ℕ → ℕ) (x : ℕ) :
    colAct c x = xorList ((List.range 10).map fun i => if x.testBit i then c i else 0) := by
  rw [colAct, xorList, List.foldr_map]
  exact foldr_if_xor _ c x

theorem colAct_xorList (c : ℕ → ℕ) (l : List ℕ) :
    colAct c (xorList l) = xorList (l.map (colAct c)) := by
  induction l with
  | nil => simpa [xorList] using colAct_zero c
  | cons a l ih =>
    show colAct c (a ^^^ xorList l) = colAct c a ^^^ xorList (l.map (colAct c))
    rw [colAct_xor, ih]

theorem colAct_comp (c d : ℕ → ℕ) (x : ℕ) :
    colAct c (colAct d x) = colAct (fun i => colAct c (d i)) x := by
  rw [colAct_eq_xorList d x, colAct_xorList, colAct_eq_xorList (fun i => colAct c (d i)) x,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases h : x.testBit i <;> simp [h, colAct_zero]

theorem colAct_ext {c c' : ℕ → ℕ} (h : ∀ i < 10, c i = c' i) (x : ℕ) :
    colAct c x = colAct c' x := by
  rw [colAct_eq_xorList, colAct_eq_xorList]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.1 hi)]

def ActsBy (g : MulAut ↥Jc) (c : ℕ → ℕ) : Prop :=
  ∀ x < 1024, g (jcA x) = jcA (colAct c x)

def TabLt (l : List ℕ) : Prop := ∀ i < 10, l.getD i 0 < 1024

theorem actsBy_congr {g : MulAut ↥Jc} {c c' : ℕ → ℕ} (h : ∀ i < 10, c i = c' i)
    (hg : ActsBy g c) : ActsBy g c' := by
  intro x hx
  rw [hg x hx, colAct_ext h x]

theorem actsBy_mul {g h : MulAut ↥Jc} {c d : ℕ → ℕ} (hd : ∀ i < 10, d i < 1024)
    (hg : ActsBy g c) (hh : ActsBy h d) :
    ActsBy (g * h) (fun i => colAct c (d i)) := by
  intro x hx
  rw [MulAut.mul_apply, hh x hx, hg _ (colAct_lt hd x), colAct_comp]

theorem actsBy_mul_list {g h : MulAut ↥Jc} {l₁ l₂ : List ℕ} (hl₂ : TabLt l₂)
    (hg : ActsBy g (Native.tabF l₁)) (hh : ActsBy h (Native.tabF l₂)) :
    ActsBy (g * h) (Native.tabF (Native.compL l₁ l₂)) := by
  refine actsBy_congr ?_ (actsBy_mul hl₂ hg hh)
  intro i hi
  simp only [Native.tabF, Native.compL, List.getD_eq_getElem, List.length_map,
    List.length_range, hi, List.getElem_map, List.getElem_range]

theorem actsBy_one : ActsBy (1 : MulAut ↥Jc) (Native.tabF Native.idTab) := by
  intro x hx
  have h := qWord_jcA_eq_colAct (w := []) (by simp) (x := x) hx
  rw [qWord_nil, MulAut.one_apply] at h
  rw [h]
  exact congrArg jcA (colAct_ext (fun i hi => by
    simp only [wordAct, List.foldr_nil, Native.tabF, Native.idTab, List.getD_eq_getElem,
      List.length_map, List.length_range, hi, List.getElem_map, List.getElem_range]) x)

theorem actsBy_qWord {w : List ℕ} (hw : ∀ k ∈ w, k < 3) :
    ActsBy (qWord w) (fun i => wordAct w (2 ^ i)) :=
  fun x hx => qWord_jcA_eq_colAct hw hx

theorem actsBy_wCols {w : List ℕ} (hw : ∀ k ∈ w, k < 3) :
    ActsBy (qWord w) (Native.tabF (Native.wCols w)) := by
  refine actsBy_congr ?_ (actsBy_qWord hw)
  intro i hi
  simp only [Native.tabF, Native.wCols, List.getD_eq_getElem, List.length_map,
    List.length_range, hi, List.getElem_map, List.getElem_range]

theorem tabLt_of_mem {l : List ℕ} (hl : l ∈ Native.tabs) : TabLt l := by
  intro i hi
  obtain ⟨hlen, hlt⟩ := tab_mem_spec hl
  have hi' : i < l.length := by omega
  rw [List.getD_eq_getElem (l := l) (n := i) (d := 0) hi']
  exact hlt l[i] (List.getElem_mem hi')

theorem tabLt_getD {i : ℕ} (hi : i < 256) : TabLt (Native.tabs.getD i []) :=
  tabLt_of_mem (by
    rw [List.getD_eq_getElem (l := Native.tabs) (n := i) (d := [])
      (by simpa [tabs_length] using hi)]
    exact List.getElem_mem (by simpa [tabs_length] using hi))

theorem compL_getD {l₁ l₂ : List ℕ} {i : ℕ} (hi : i < 10) :
    (Native.compL l₁ l₂).getD i 0 = colAct (Native.tabF l₁) (l₂.getD i 0) := by
  simp only [Native.tabF, Native.compL, List.getD_eq_getElem, List.length_map,
    List.length_range, hi, List.getElem_map, List.getElem_range]

theorem tabLt_compL {l₁ l₂ : List ℕ} (h : TabLt l₁) : TabLt (Native.compL l₁ l₂) := by
  intro i hi
  rw [compL_getD hi]
  exact colAct_lt h _

noncomputable def sylS : Subgroup (MulAut ↥Jc) :=
  closure (Set.range fun k : Fin 4 => qWord (Data.sylW.getD (k : ℕ) []))

theorem sylW_getD_mem {k : ℕ} (hk : k < 4) : Data.sylW.getD k [] ∈ Data.sylW := by
  have hk' : k < Data.sylW.length := by simpa [Data.sylW] using hk
  rw [List.getD_eq_getElem (l := Data.sylW) (n := k) (d := []) hk']
  exact List.getElem_mem hk'

theorem sylW_getD_lt3 {k : ℕ} (hk : k < 4) : ∀ j ∈ Data.sylW.getD k [], j < 3 :=
  words_lt3 _ (sylW_getD_mem hk)

theorem qWord_sylW_mem {k : ℕ} (hk : k < 4) : qWord (Data.sylW.getD k []) ∈ sylS :=
  Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩

theorem sylS_le_Qj : sylS ≤ Qj := by
  rw [sylS, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact qWord_mem (sylW_getD_lt3 k.2)

theorem gens_getD {k : ℕ} (hk : k < 4) :
    Native.gens.getD k [] = Native.wCols (Data.sylW.getD k []) := by
  have hlen : k < Native.gens.length := by rw [gens_length]; exact hk
  rw [List.getD_eq_getElem (l := Native.gens) (n := k) (d := []) hlen]
  simp only [Native.gens, List.getElem_map, List.getElem_range]

theorem actsBy_gen {k : ℕ} (hk : k < 4) :
    ActsBy (qWord (Data.sylW.getD k [])) (Native.tabF (Native.gens.getD k [])) := by
  rw [gens_getD hk]
  exact actsBy_wCols (sylW_getD_lt3 hk)

theorem qWord_flatMap_replicate (n k : ℕ) :
    qWord ((List.replicate n k).flatMap fun j => Data.sylW.getD j []) =
      (qWord (Data.sylW.getD k [])) ^ n := by
  induction n with
  | zero => simp [qWord_nil]
  | succ n ih =>
    rw [List.replicate_succ, List.flatMap_cons, qWord_append, ih, pow_succ']

private theorem exists_word_aux {g : MulAut ↥Jc} (hg : g ∈ sylS) :
    ∃ u : List ℕ, (∀ k ∈ u, k < 4) ∧
      qWord (u.flatMap fun j => Data.sylW.getD j []) = g := by
  haveI : Finite ↥Jc :=
    Finite.of_surjective (fun m : Fin 1024 => jcA m) fun x => by
      obtain ⟨m, hm, hx⟩ := exists_jcA x
      exact ⟨⟨m, hm⟩, hx⟩
  haveI : Finite (MulAut ↥Jc) := inferInstance
  rw [sylS] at hg
  refine Subgroup.closure_induction_left
    (s := Set.range fun k : Fin 4 => qWord (Data.sylW.getD (k : ℕ) []))
    ?one ?mul ?inv hg
  · exact ⟨[], by simp, qWord_nil⟩
  · intro x hx y hy ih
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨u, hu, hqu⟩ := ih
    refine ⟨(k : ℕ) :: u, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact k.2
      · exact hu j hj
    · rw [List.flatMap_cons, qWord_append, hqu]
  · intro x hx y hy ih
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨u, hu, hqu⟩ := ih
    let n := orderOf (qWord (Data.sylW.getD (k : ℕ) [])) - 1
    have hinv : (qWord (Data.sylW.getD (k : ℕ) [])) ^ n =
        (qWord (Data.sylW.getD (k : ℕ) []))⁻¹ := by
      have hpos : 0 < orderOf (qWord (Data.sylW.getD (k : ℕ) [])) := orderOf_pos _
      have h1 : n + 1 = orderOf (qWord (Data.sylW.getD (k : ℕ) [])) := by
        show orderOf (qWord (Data.sylW.getD (k : ℕ) [])) - 1 + 1 = _
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
      have hmul : (qWord (Data.sylW.getD (k : ℕ) [])) ^ n *
          qWord (Data.sylW.getD (k : ℕ) []) = 1 := by
        rw [← pow_succ, h1, pow_orderOf_eq_one]
      exact eq_inv_of_mul_eq_one_left hmul
    refine ⟨List.replicate n (k : ℕ) ++ u, ?_, ?_⟩
    · intro j hj
      rcases List.mem_append.1 hj with hj | hj
      · rw [List.mem_replicate] at hj
        exact hj.2 ▸ k.2
      · exact hu j hj
    · rw [List.flatMap_append, qWord_append, qWord_flatMap_replicate, hinv, hqu]

theorem exists_word {g : MulAut ↥Jc} (hg : g ∈ sylS) :
    ∃ u : List ℕ, (∀ k ∈ u, k < 4) ∧
      qWord (u.flatMap fun j => Data.sylW.getD j []) = g :=
  exists_word_aux hg

theorem idTab_mem : Native.idTab ∈ Native.tabs := by
  rw [← tabs_zero]
  exact List.getD_eq_getElem (l := Native.tabs) (n := 0) (d := [])
    (by simpa [tabs_length]) ▸ List.getElem_mem (by simpa [tabs_length] :
      0 < Native.tabs.length)

theorem actsBy_word : ∀ u : List ℕ, (∀ k ∈ u, k < 4) →
    ∃ l ∈ Native.tabs, ActsBy (qWord (u.flatMap fun j => Data.sylW.getD j [])) (Native.tabF l) := by
  intro u
  induction u with
  | nil =>
    intro _
    refine ⟨Native.idTab, idTab_mem, ?_⟩
    simpa [qWord_nil] using actsBy_one
  | cons k u ih =>
    intro hu
    have hk : k < 4 := hu k (List.mem_cons_self ..)
    have hu' : ∀ j ∈ u, j < 4 := fun j hj => hu j (List.mem_cons_of_mem _ hj)
    obtain ⟨l, hl, hActs⟩ := ih hu'
    rw [List.flatMap_cons, qWord_append]
    exact ⟨Native.compL (Native.gens.getD k []) l, closed_spec_mem hl hk,
      actsBy_mul_list (tabLt_of_mem hl) (actsBy_gen hk) hActs⟩

theorem actsBy_mem_tabs {g : MulAut ↥Jc} (hg : g ∈ sylS) :
    ∃ l ∈ Native.tabs, ActsBy g (Native.tabF l) := by
  obtain ⟨u, hu, hqu⟩ := exists_word hg
  obtain ⟨l, hl, h⟩ := actsBy_word u hu
  exact ⟨l, hl, hqu ▸ h⟩

theorem actsBy_elem {g h : MulAut ↥Jc} {l : List ℕ} (a₁ : ActsBy g (Native.tabF l))
    (a₂ : ActsBy h (Native.tabF l)) : g = h := by
  apply mulAut_ext_basis
  intro i hi
  rw [a₁ (2 ^ i) (two_pow_lt_1024 hi), a₂ (2 ^ i) (two_pow_lt_1024 hi)]

theorem actsBy_eq_table' {g : MulAut ↥Jc} {l₁ l₂ : List ℕ}
    (h₁ : l₁.length = 10) (h₂ : l₂.length = 10) (hlt₁ : TabLt l₁) (hlt₂ : TabLt l₂)
    (a₁ : ActsBy g (Native.tabF l₁)) (a₂ : ActsBy g (Native.tabF l₂)) : l₁ = l₂ := by
  have key : ∀ i < 10, l₁.getD i 0 = l₂.getD i 0 := by
    intro i hi
    have e1 : g (jcA (2 ^ i)) = jcA (l₁.getD i 0) := by
      rw [a₁ (2 ^ i) (two_pow_lt_1024 hi), colAct_two_pow _ hi]
      rfl
    have e2 : g (jcA (2 ^ i)) = jcA (l₂.getD i 0) := by
      rw [a₂ (2 ^ i) (two_pow_lt_1024 hi), colAct_two_pow _ hi]
      rfl
    exact (jcA_inj (hlt₁ i hi) (hlt₂ i hi)).1 (e1.symm.trans e2)
  apply List.ext_getElem
  · omega
  · intro i hi₁ hi₂
    rw [← List.getD_eq_getElem (l := l₁) (n := i) (d := 0) hi₁,
      ← List.getD_eq_getElem (l := l₂) (n := i) (d := 0) hi₂]
    exact key i (by omega)

theorem idTab_length : Native.idTab.length = 10 := by
  simp only [Native.idTab, List.length_map, List.length_range]

theorem idTab_getD {i : ℕ} (hi : i < 10) : Native.idTab.getD i 0 = 2 ^ i := by
  have hlen : i < (List.range 10).length := by simpa using hi
  rw [show Native.idTab = (List.range 10).map (fun j => 2 ^ j) from rfl]
  rw [List.getD_eq_getElem (l := (List.range 10).map (fun j => 2 ^ j)) (n := i) (d := 0)
    (by simpa using hlen)]
  rw [List.getElem_map, List.getElem_range]

theorem actsBy_eq_table {g : MulAut ↥Jc} {l₁ l₂ : List ℕ}
    (h₁ : l₁ ∈ Native.tabs) (h₂ : l₂ ∈ Native.tabs)
    (a₁ : ActsBy g (Native.tabF l₁)) (a₂ : ActsBy g (Native.tabF l₂)) : l₁ = l₂ :=
  actsBy_eq_table' (tab_mem_spec h₁).1 (tab_mem_spec h₂).1 (tabLt_of_mem h₁) (tabLt_of_mem h₂)
    a₁ a₂

theorem tab_mem_getD {i : ℕ} (hi : i < 256) : Native.tabs.getD i [] ∈ Native.tabs := by
  rw [List.getD_eq_getElem (l := Native.tabs) (n := i) (d := [])
    (by simpa [tabs_length] using hi)]
  exact List.getElem_mem (by simpa [tabs_length] using hi)

theorem tab_getD_inj {i j : ℕ} (hi : i < 256) (hj : j < 256)
    (h : Native.tabs.getD i [] = Native.tabs.getD j []) : i = j := by
  by_contra hij
  exact nodup_spec hi hj hij h

theorem realized : ∀ i, i < 256 →
    ∃ g ∈ sylS, ActsBy g (Native.tabF (Native.tabs.getD i [])) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h0 : i = 0
    · subst h0
      exact ⟨1, sylS.one_mem, by rw [tabs_zero]; exact actsBy_one⟩
    · obtain ⟨p, hp, k, hk, htab⟩ := parent_spec (by simpa [tabs_length] using hi) h0
      obtain ⟨g, hgS, hgActs⟩ := ih p hp (by omega)
      refine ⟨qWord (Data.sylW.getD k []) * g, sylS.mul_mem (qWord_sylW_mem hk) hgS, ?_⟩
      rw [htab]
      exact actsBy_mul_list (tabLt_getD (by omega)) (actsBy_gen hk) hgActs

noncomputable def sylG (i : Fin 256) : ↥sylS :=
  ⟨(realized i.val i.isLt).choose, (realized i.val i.isLt).choose_spec.1⟩

theorem sylG_acts (i : Fin 256) :
    ActsBy (sylG i : MulAut ↥Jc) (Native.tabF (Native.tabs.getD i.val [])) :=
  (realized i.val i.isLt).choose_spec.2

theorem sylG_inj : Function.Injective sylG := by
  intro i j hij
  apply Fin.ext
  apply tab_getD_inj i.isLt j.isLt
  have h1 := sylG_acts i
  rw [hij] at h1
  exact actsBy_eq_table (tab_mem_getD i.isLt) (tab_mem_getD j.isLt) h1 (sylG_acts j)

theorem idx_exists (g : ↥sylS) :
    ∃ i : Fin 256, ActsBy (g : MulAut ↥Jc) (Native.tabF (Native.tabs.getD i.val [])) := by
  obtain ⟨l, hl, hacts⟩ := actsBy_mem_tabs g.2
  have hlt : Native.tabs.idxOf l < 256 := by
    rw [← tabs_length]; exact List.idxOf_lt_length_iff.mpr hl
  refine ⟨⟨Native.tabs.idxOf l, hlt⟩, ?_⟩
  rw [show Native.tabs.getD (Native.tabs.idxOf l) [] = l from ?_]
  · exact hacts
  · rw [List.getD_eq_getElem?_getD, List.getElem?_idxOf hl]
    rfl

noncomputable def sylIdx (g : ↥sylS) : Fin 256 := (idx_exists g).choose

theorem idx_acts (g : ↥sylS) :
    ActsBy (g : MulAut ↥Jc) (Native.tabF (Native.tabs.getD (sylIdx g).val [])) :=
  (idx_exists g).choose_spec

theorem idx_inj : Function.Injective sylIdx := by
  intro g h hgh
  have ha := idx_acts g
  have hb := idx_acts h
  have hidx : (sylIdx g).val = (sylIdx h).val := by rw [hgh]
  rw [hidx] at ha
  exact Subtype.ext (actsBy_elem ha hb)

theorem sylG_surj : Function.Surjective sylG := by
  intro g
  refine ⟨sylIdx g, ?_⟩
  apply Subtype.ext
  exact (actsBy_elem (idx_acts g) (sylG_acts (sylIdx g))).symm

theorem card_sylS : Nat.card ↥sylS = 256 := by
  haveI : Finite ↥Jc :=
    Finite.of_surjective (fun m : Fin 1024 => jcA m) fun x => by
      obtain ⟨m, hm, hx⟩ := exists_jcA x
      exact ⟨⟨m, hm⟩, hx⟩
  haveI : Finite (MulAut ↥Jc) := inferInstance
  have h1 : 256 ≤ Nat.card ↥sylS := by
    have := Nat.card_le_card_of_injective sylG sylG_inj
    simpa using this
  have h2 : Nat.card ↥sylS ≤ 256 := by
    have := Nat.card_le_card_of_injective sylIdx idx_inj
    simpa using this
  omega

noncomputable def sylE : Fin 256 ≃ ↥sylS := Equiv.ofBijective sylG ⟨sylG_inj, sylG_surj⟩

theorem sylE_apply (i : Fin 256) : sylE i = sylG i := Equiv.ofBijective_apply _ _ _

theorem sylE_acts (i : Fin 256) :
    ActsBy (sylE i : MulAut ↥Jc) (Native.tabF (Native.tabs.getD i.val [])) := by
  rw [sylE_apply]
  exact sylG_acts i

theorem sylE_zero : sylE (0 : Fin 256) = 1 := by
  apply Subtype.ext
  refine actsBy_elem (l := Native.idTab) ?_ actsBy_one
  have h := sylE_acts (0 : Fin 256)
  rw [show (0 : Fin 256).val = 0 from rfl, tabs_zero] at h
  exact h

noncomputable def elemOf (i : ℕ) : ↥sylS := if h : i < 256 then sylE ⟨i, h⟩ else 1

theorem elemOf_apply {i : ℕ} (hi : i < 256) : elemOf i = sylE ⟨i, hi⟩ := dif_pos hi

theorem elemOf_acts {i : ℕ} (hi : i < 256) :
    ActsBy (elemOf i : MulAut ↥Jc) (Native.tabF (Native.tabs.getD i [])) := by
  rw [elemOf_apply hi]
  exact sylE_acts ⟨i, hi⟩

theorem elemOf_zero : elemOf 0 = 1 := by
  rw [elemOf_apply (by norm_num : 0 < 256)]
  simpa using sylE_zero

theorem elemOf_symm (z : ↥sylS) :
    (elemOf (sylE.symm z).val : MulAut ↥Jc) = (z : MulAut ↥Jc) := by
  rw [elemOf_apply (sylE.symm z).isLt]
  have h : (⟨(sylE.symm z).val, (sylE.symm z).isLt⟩ : Fin 256) = sylE.symm z := rfl
  rw [h, Equiv.apply_symm_apply]

theorem elemOf_inj {i j : ℕ} (hi : i < 256) (hj : j < 256) (h : elemOf i = elemOf j) : i = j := by
  have h' : (⟨i, hi⟩ : Fin 256) = ⟨j, hj⟩ := by
    apply sylE.injective
    rw [← elemOf_apply hi, ← elemOf_apply hj]
    exact h
  exact congrArg Fin.val h'

theorem elemOf_mul {s i : ℕ} (hs : s < 256) (hi : i < 256) :
    elemOf (Native.mulIdxC s i) = elemOf s * elemOf i := by
  obtain ⟨hlt, htab⟩ := mulIdx_spec hs hi
  have hprod : ActsBy (elemOf s * elemOf i : MulAut ↥Jc)
      (Native.tabF (Native.tabs.getD (Native.mulIdxC s i) [])) := by
    rw [htab]
    exact actsBy_mul_list (tabLt_getD hi) (elemOf_acts hs) (elemOf_acts hi)
  apply Subtype.ext
  exact (actsBy_elem hprod (elemOf_acts hlt)).symm

theorem mulIdx_zero {s : ℕ} (hs : s < 256) : Native.mulIdxC s 0 = s := by
  apply elemOf_inj (mulIdx_spec hs (by norm_num)).1 hs
  rw [elemOf_mul hs (by norm_num), elemOf_zero, mul_one]

theorem elemOf_ne_one {i : ℕ} (hi : i < 256) : elemOf i ≠ 1 ↔ i ≠ 0 := by
  constructor
  · intro h h0
    apply h
    rw [h0]
    exact elemOf_zero
  · intro h h1
    exact h (elemOf_inj hi (by norm_num) (by rw [h1, elemOf_zero]))

noncomputable def idxListOf (Z : Subgroup (MulAut ↥Jc)) : List ℕ := by
  classical
  exact (List.range 256).filter fun i => decide ((elemOf i : MulAut ↥Jc) ∈ Z)

theorem mem_idxListOf {Z : Subgroup (MulAut ↥Jc)} {i : ℕ} :
    i ∈ idxListOf Z ↔ i < 256 ∧ (elemOf i : MulAut ↥Jc) ∈ Z := by
  classical
  simp only [idxListOf, List.mem_filter, List.mem_range, decide_eq_true_eq]

theorem idxListOf_nodup (Z : Subgroup (MulAut ↥Jc)) : (idxListOf Z).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem card_idxListOf {Z : Subgroup (MulAut ↥Jc)} (hZ : Z ≤ sylS) :
    Nat.card Z = (idxListOf Z).length := by
  have hcard : Nat.card {i // i ∈ idxListOf Z} = (idxListOf Z).length := by
    rw [← Nat.card_fin (idxListOf Z).length]
    exact Nat.card_congr (List.Nodup.getEquiv (idxListOf Z) (idxListOf_nodup Z)).symm
  rw [← hcard]
  refine Nat.card_congr ?_
  refine
    { toFun := fun z => ⟨(sylE.symm ⟨z.1, hZ z.2⟩).val, ?_⟩
      invFun := fun i => ⟨(elemOf i.1 : MulAut ↥Jc), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [mem_idxListOf]
    exact ⟨(sylE.symm ⟨z.1, hZ z.2⟩).isLt, by rw [elemOf_symm]; exact z.2⟩
  · exact (mem_idxListOf.mp i.2).2
  · intro z
    apply Subtype.ext
    exact elemOf_symm ⟨z.1, hZ z.2⟩
  · intro i
    apply Subtype.ext
    show (sylE.symm (elemOf i.1)).val = i.1
    have h1 : (elemOf i.1 : ↥sylS) = sylE ⟨i.1, (mem_idxListOf.mp i.2).1⟩ :=
      elemOf_apply (mem_idxListOf.mp i.2).1
    rw [h1, Equiv.symm_apply_apply]

theorem fixedB_eq (l : List ℕ) (m : Fin 1024) :
    Native.fixedB l m = true ↔ Native.fixed l m := by
  simp only [Native.fixedB, Native.fixed, List.all_eq_true, beq_iff_eq]

noncomputable def fixCountF (s : Finset ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin 1024)).filter fun m =>
    ∀ i ∈ s, colAct (Native.tabF (Native.tabs.getD i [])) m.val = m.val).card

theorem fixCount_eq_finset (l : List ℕ) : Native.fixCount l = fixCountF l.toFinset := by
  classical
  rw [Native.fixCount, fixCountF]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro m _
  simp only [fixedB_eq, Native.fixed, List.mem_toFinset]

theorem fixCount_eq_fixed (l : List ℕ) [DecidablePred (Native.fixed l)] :
    Native.fixCount l = ((Finset.univ : Finset (Fin 1024)).filter (Native.fixed l)).card := by
  classical
  rw [Native.fixCount]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro m _
  exact fixedB_eq l m

theorem card_fixed_eq {Z : Subgroup (MulAut ↥Jc)} (hZ : Z ≤ sylS) :
    Nat.card {a : ↥Jc // ∀ z ∈ Z, z a = a} = Native.fixCount (idxListOf Z) := by
  classical
  have hbij : Nat.card {a : ↥Jc // ∀ z ∈ Z, z a = a} =
      Nat.card {m : Fin 1024 // Native.fixed (idxListOf Z) m} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun a => ⟨⟨coord a.1, coord_lt a.1⟩, ?_⟩
        invFun := fun m => ⟨jcA m.1.val, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro i hi
      obtain ⟨hlt, hZi⟩ := mem_idxListOf.mp hi
      have ha : (elemOf i : MulAut ↥Jc) a.1 = a.1 := a.2 (elemOf i) hZi
      have hacts : (elemOf i : MulAut ↥Jc) (jcA (coord a.1)) =
          jcA (colAct (Native.tabF (Native.tabs.getD i [])) (coord a.1)) :=
        elemOf_acts hlt (coord a.1) (coord_lt a.1)
      rw [jcA_coord] at hacts
      have hfix : colAct (Native.tabF (Native.tabs.getD i [])) (coord a.1) = coord a.1 :=
        (jcA_inj (colAct_lt (tabLt_getD hlt) _) (coord_lt a.1)).1
          ((hacts.symm.trans ha).trans (jcA_coord a.1).symm)
      exact hfix
    · intro z hz
      have hzS : z ∈ sylS := hZ hz
      have hmem : (sylE.symm ⟨z, hzS⟩).val ∈ idxListOf Z := by
        rw [mem_idxListOf]
        exact ⟨(sylE.symm _).isLt, by rw [elemOf_symm]; exact hz⟩
      have hacts := elemOf_acts (sylE.symm ⟨z, hzS⟩).isLt (m.1.val) m.1.isLt
      rw [elemOf_symm] at hacts
      have hfix := m.2 _ hmem
      rw [hacts, hfix]
    · intro a
      apply Subtype.ext
      exact jcA_coord a.1
    · intro m
      apply Subtype.ext
      apply Fin.ext
      exact coord_jcA m.1.isLt
  rw [hbij, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (fixCount_eq_fixed (idxListOf Z)).symm

theorem mem_pairOf {s i : ℕ} (hi : i < 256) :
    i ∈ Native.pairOf s ↔ i = 0 ∨ i = s := by
  rw [Native.pairOf, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨-, hc⟩
    simpa using hc
  · rintro (rfl | rfl)
    · exact ⟨hi, by simp⟩
    · exact ⟨hi, by simp⟩

theorem compL_eq_idTab_of_mul_eq_one {s : ℕ} (hs : s < 256)
    (h : (elemOf s : MulAut ↥Jc) * elemOf s = 1) :
    Native.compL (Native.tabs.getD s []) (Native.tabs.getD s []) = Native.idTab := by
  have hact : ActsBy ((elemOf s : MulAut ↥Jc) * elemOf s)
      (Native.tabF (Native.compL (Native.tabs.getD s []) (Native.tabs.getD s []))) :=
    actsBy_mul_list (tabLt_getD hs) (elemOf_acts hs) (elemOf_acts hs)
  rw [h] at hact
  have hlen : (Native.compL (Native.tabs.getD s []) (Native.tabs.getD s [])).length = 10 := by
    simp [Native.compL]
  have hllt : TabLt (Native.compL (Native.tabs.getD s []) (Native.tabs.getD s [])) :=
    tabLt_compL (tabLt_getD hs)
  apply List.ext_getElem
  · rw [hlen, idTab_length]
  · intro i hi₁ hi₂
    have hi : i < 10 := by rw [hlen] at hi₁; exact hi₁
    rw [← List.getD_eq_getElem (l := Native.compL (Native.tabs.getD s []) (Native.tabs.getD s []))
        (n := i) (d := 0) hi₁,
      ← List.getD_eq_getElem (l := Native.idTab) (n := i) (d := 0) hi₂]
    have h1 : (Native.compL (Native.tabs.getD s []) (Native.tabs.getD s [])).getD i 0 = 2 ^ i := by
      have h2 := hact (2 ^ i) (two_pow_lt_1024 hi)
      rw [MulAut.one_apply, colAct_two_pow _ hi] at h2
      exact (jcA_inj (hllt i hi) (two_pow_lt_1024 hi)).1 h2.symm
    rw [h1, idTab_getD hi]

theorem compL_comm {s i : ℕ} (hs : s < 256) (hi : i < 256)
    (h : (elemOf s : MulAut ↥Jc) * elemOf i = elemOf i * elemOf s) :
    Native.compL (Native.tabs.getD s []) (Native.tabs.getD i []) =
      Native.compL (Native.tabs.getD i []) (Native.tabs.getD s []) := by
  have h1 : ActsBy ((elemOf s : MulAut ↥Jc) * elemOf i)
      (Native.tabF (Native.compL (Native.tabs.getD s []) (Native.tabs.getD i []))) :=
    actsBy_mul_list (tabLt_getD hi) (elemOf_acts hs) (elemOf_acts hi)
  have h2 : ActsBy ((elemOf s : MulAut ↥Jc) * elemOf i)
      (Native.tabF (Native.compL (Native.tabs.getD i []) (Native.tabs.getD s []))) := by
    rw [h]
    exact actsBy_mul_list (tabLt_getD hs) (elemOf_acts hi) (elemOf_acts hs)
  exact actsBy_eq_table' (by simp [Native.compL]) (by simp [Native.compL])
    (tabLt_compL (tabLt_getD hs)) (tabLt_compL (tabLt_getD hi)) h1 h2

theorem idxListOf_mul_fix_le {Z : Subgroup (MulAut ↥Jc)} (hZS : Z ≤ sylS)
    (hZ : IsElementaryAbelian 2 Z) (hZ1 : Z ≠ ⊥) :
    (idxListOf Z).length * Native.fixCount (idxListOf Z) ≤ 512 := by
  haveI : IsElementaryAbelian 2 Z := hZ
  have hne : ∃ z : MulAut ↥Jc, z ∈ Z ∧ z ≠ 1 := by
    by_contra h
    apply hZ1
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    by_contra hz1
    exact h ⟨z, hz, hz1⟩
  obtain ⟨z, hzZ, hz1⟩ := hne
  have hz2 : z * z = 1 := by
    have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Z) z hzZ
    rwa [pow_two] at h
  set s : ℕ := (sylE.symm ⟨z, hZS hzZ⟩).val with hsdef
  have hs_lt : s < 256 := (sylE.symm ⟨z, hZS hzZ⟩).isLt
  have hs_elem : (elemOf s : MulAut ↥Jc) = z := elemOf_symm ⟨z, hZS hzZ⟩
  have h0mem : 0 ∈ idxListOf Z := by
    rw [mem_idxListOf]
    exact ⟨by norm_num, by rw [elemOf_zero]; exact Z.one_mem⟩
  have hs_ne0 : s ≠ 0 := by
    intro h0
    apply hz1
    rw [← hs_elem, h0]
    exact congrArg Subtype.val elemOf_zero
  have hs_invtab : Native.compL (Native.tabs.getD s []) (Native.tabs.getD s []) =
      Native.idTab := by
    apply compL_eq_idTab_of_mul_eq_one hs_lt
    rw [hs_elem]
    exact hz2
  have key : ∀ n : ℕ, ∀ l : List ℕ, l ∈ Native.subs →
      (∀ i ∈ l, i ∈ idxListOf Z) →
      (idxListOf Z).length - l.length = n →
      ∃ l' ∈ Native.subs, (∀ i ∈ l', i ∈ idxListOf Z) ∧
        l'.length = (idxListOf Z).length := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro l hl hsub hlen
      by_cases hfull : l.length = (idxListOf Z).length
      · exact ⟨l, hl, hsub, hfull⟩
      · have hex : ∃ s', s' ∈ idxListOf Z ∧ s' ∉ l := by
          by_contra h
          push Not at h
          have hle : l.length = (idxListOf Z).length := by
            have hf1 : (idxListOf Z).toFinset ⊆ l.toFinset := by
              intro x hx
              rw [List.mem_toFinset] at hx ⊢
              exact h x hx
            have hf2 : l.toFinset ⊆ (idxListOf Z).toFinset := by
              intro x hx
              rw [List.mem_toFinset] at hx ⊢
              exact hsub x hx
            have heq : (idxListOf Z).toFinset = l.toFinset := Finset.Subset.antisymm hf1 hf2
            rw [← List.toFinset_card_of_nodup (idxListOf_nodup Z),
              ← List.toFinset_card_of_nodup (subs_mem_spec hl).2, heq]
          exact hfull hle
        obtain ⟨s', hs'Z, hs'l⟩ := hex
        have hs'_lt : s' < 256 := (mem_idxListOf.mp hs'Z).1
        have hs'Z' : (elemOf s' : MulAut ↥Jc) ∈ Z := (mem_idxListOf.mp hs'Z).2
        have h0l : 0 ∈ l := (subs_mem_spec hl).1.1
        have hs'_ne0 : s' ≠ 0 := fun h0 => hs'l (h0 ▸ h0l)
        have hs'_inv2 : (elemOf s' : MulAut ↥Jc) * (elemOf s' : MulAut ↥Jc) = 1 := by
          have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Z) (elemOf s') hs'Z'
          rwa [pow_two] at h
        have hs'_ne1 : (elemOf s' : ↥sylS) ≠ 1 := by
          intro h1
          exact (elemOf_ne_one hs'_lt).mpr hs'_ne0 h1
        have hs'_tab : Native.tabs.getD s' [] ≠ Native.idTab := by
          intro h
          apply hs'_ne1
          have hact : ActsBy (elemOf s' : MulAut ↥Jc) (Native.tabF Native.idTab) := by
            rw [← h]
            exact elemOf_acts hs'_lt
          exact Subtype.ext (actsBy_elem hact actsBy_one)
        have hs'_invtab : Native.compL (Native.tabs.getD s' []) (Native.tabs.getD s' []) =
            Native.idTab := compL_eq_idTab_of_mul_eq_one hs'_lt hs'_inv2
        have hcomm : Native.commutesAll s' l = true := by
          rw [Native.commutesAll, List.all_eq_true]
          intro i hi
          have hi_lt : i < 256 := (mem_idxListOf.mp (hsub i hi)).1
          have hiZ : (elemOf i : MulAut ↥Jc) ∈ Z := (mem_idxListOf.mp (hsub i hi)).2
          have hcommZ : (elemOf s' : MulAut ↥Jc) * elemOf i = elemOf i * elemOf s' := by
            have h := mul_comm (⟨(elemOf s' : MulAut ↥Jc), hs'Z'⟩ : Z)
              ⟨(elemOf i : MulAut ↥Jc), hiZ⟩
            simpa using congrArg Subtype.val h
          simpa using compL_comm hs'_lt hi_lt hcommZ
        have hstep : Native.stepL l s' ∈ Native.subs :=
          step_spec hl hs'_lt hs'l hs'_tab hs'_invtab hcomm
        have hstep_sub : ∀ i ∈ Native.stepL l s', i ∈ idxListOf Z := by
          intro i hi
          rw [Native.stepL, List.mem_filter] at hi
          obtain ⟨hir, hic⟩ := hi
          rw [List.mem_range] at hir
          have hic' : i ∈ l ∨ i ∈ l.map (Native.mulIdxC s') := by
            rw [List.contains_eq_mem, List.contains_eq_mem] at hic
            simpa using hic
          rcases hic' with hi | hi
          · exact hsub i hi
          · rw [List.mem_map] at hi
            obtain ⟨j, hj, rfl⟩ := hi
            have hjZ := (mem_idxListOf.mp (hsub j hj)).2
            have hj_lt := (mem_idxListOf.mp (hsub j hj)).1
            have hmi := mulIdx_spec hs'_lt hj_lt
            rw [mem_idxListOf]
            refine ⟨hmi.1, ?_⟩
            rw [elemOf_mul hs'_lt hj_lt]
            exact Z.mul_mem hs'Z' hjZ
        have hsub_l : ∀ i ∈ l, i ∈ Native.stepL l s' := by
          intro i hi
          rw [Native.stepL, List.mem_filter]
          refine ⟨List.mem_range.mpr (by have := (subs_mem_spec hl).1.2 i hi; omega), ?_⟩
          rw [List.contains_eq_mem, show decide (i ∈ l) = true from by simpa using hi,
            Bool.true_or]
        have hs'_step : s' ∈ Native.stepL l s' := by
          rw [Native.stepL, List.mem_filter]
          refine ⟨List.mem_range.mpr hs'_lt, ?_⟩
          rw [List.contains_eq_mem, List.contains_eq_mem,
            show decide (s' ∈ l) = false from by
              rw [decide_eq_false_iff_not]; exact hs'l,
            Bool.false_or, decide_eq_true_eq]
          exact List.mem_map.mpr ⟨0, h0l, mulIdx_zero hs'_lt⟩
        have hnodup_step : (Native.stepL l s').Nodup := List.Nodup.filter _ List.nodup_range
        have hlt_len : l.length < (Native.stepL l s').length := by
          have hf : l.toFinset ⊆ (Native.stepL l s').toFinset := by
            intro x hx
            rw [List.mem_toFinset] at hx ⊢
            exact hsub_l x hx
          have hle : l.length ≤ (Native.stepL l s').length := by
            have hcard := Finset.card_le_card hf
            rwa [List.toFinset_card_of_nodup (subs_mem_spec hl).2,
              List.toFinset_card_of_nodup hnodup_step] at hcard
          rcases lt_or_eq_of_le hle with h | h
          · exact h
          · exfalso
            apply hs'l
            have heq : l.toFinset = (Native.stepL l s').toFinset := by
              apply Finset.eq_of_subset_of_card_le hf
              rw [List.toFinset_card_of_nodup hnodup_step,
                List.toFinset_card_of_nodup (subs_mem_spec hl).2, ← h]
            rw [← List.mem_toFinset, heq, List.mem_toFinset]
            exact hs'_step
        have hlc : l.length ≤ (idxListOf Z).length := by
          have hf : l.toFinset ⊆ (idxListOf Z).toFinset := by
            intro x hx
            rw [List.mem_toFinset] at hx ⊢
            exact hsub x hx
          have hcard := Finset.card_le_card hf
          rwa [List.toFinset_card_of_nodup (subs_mem_spec hl).2,
            List.toFinset_card_of_nodup (idxListOf_nodup Z)] at hcard
        have hsc : (Native.stepL l s').length ≤ (idxListOf Z).length := by
          have hf : (Native.stepL l s').toFinset ⊆ (idxListOf Z).toFinset := by
            intro x hx
            rw [List.mem_toFinset] at hx ⊢
            exact hstep_sub x hx
          have hcard := Finset.card_le_card hf
          rwa [List.toFinset_card_of_nodup hnodup_step,
            List.toFinset_card_of_nodup (idxListOf_nodup Z)] at hcard
        exact ih ((idxListOf Z).length - (Native.stepL l s').length) (by omega)
          (Native.stepL l s') hstep hstep_sub (by omega)
  have hpair : Native.pairOf s ∈ Native.subs := by
    have hs_tab : Native.tabs.getD s [] ≠ Native.idTab := by
      intro h
      apply hz1
      rw [← hs_elem]
      have hact : ActsBy (elemOf s : MulAut ↥Jc) (Native.tabF Native.idTab) := by
        rw [← h]
        exact elemOf_acts hs_lt
      exact actsBy_elem hact actsBy_one
    exact invol_spec hs_lt hs_ne0 hs_tab hs_invtab
  have hpair_sub : ∀ i ∈ Native.pairOf s, i ∈ idxListOf Z := by
    intro i hi
    have hi' : i < 256 := (subs_mem_spec hpair).1.2 i hi
    rw [mem_pairOf hi'] at hi
    rcases hi with rfl | rfl
    · exact h0mem
    · rw [mem_idxListOf]
      exact ⟨hs_lt, by rw [hs_elem]; exact hzZ⟩
  obtain ⟨l', hl', hsub', hlen'⟩ := key ((idxListOf Z).length - (Native.pairOf s).length)
    (Native.pairOf s) hpair hpair_sub rfl
  have hfin : l'.toFinset = (idxListOf Z).toFinset := by
    have hf : l'.toFinset ⊆ (idxListOf Z).toFinset := by
      intro x hx
      rw [List.mem_toFinset] at hx ⊢
      exact hsub' x hx
    apply Finset.eq_of_subset_of_card_le hf
    rw [List.toFinset_card_of_nodup (idxListOf_nodup Z),
      List.toFinset_card_of_nodup (subs_mem_spec hl').2, hlen']
  have hfix : Native.fixCount l' = Native.fixCount (idxListOf Z) := by
    rw [fixCount_eq_finset l', fixCount_eq_finset (idxListOf Z), hfin]
  have hb := bound_spec hl'
  rw [hfix, hlen'] at hb
  exact hb

theorem card_mul_fixed_le {Z : Subgroup (MulAut ↥Jc)} (hZS : Z ≤ sylS)
    (hZ : IsElementaryAbelian 2 Z) (hZ1 : Z ≠ ⊥) :
    Nat.card Z * Nat.card {a : ↥Jc // ∀ z ∈ Z, z a = a} ≤ 512 := by
  rw [card_idxListOf hZS, card_fixed_eq hZS]
  exact idxListOf_mul_fix_le hZS hZ hZ1

theorem card_subgroupOf_eq {sylG : Type*} [Group sylG] {H K : Subgroup sylG} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem card_sylS_subgroupOf : Nat.card (sylS.subgroupOf Qj) = 256 := by
  rw [card_subgroupOf_eq sylS_le_Qj, card_sylS]

theorem factorization_card_Qj : (887040).factorization 2 = 8 := by
  have h : (887040 : ℕ) = 2 ^ 8 * 3465 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3465)]

noncomputable def sylSylow : Sylow 2 Qj :=
  Sylow.ofCard (sylS.subgroupOf Qj)
    (by rw [card_sylS_subgroupOf, card_Qj, factorization_card_Qj]; norm_num)

theorem map_conj_le_sylS {Y : Subgroup (MulAut ↥Jc)} (hYQ : Y ≤ Qj)
    {P : Sylow 2 Qj} (hY'P : Y.subgroupOf Qj ≤ P) {g : Qj} (hg : g • P = sylSylow) :
    Y.map (MulAut.conj (g : MulAut ↥Jc)).toMonoidHom ≤ sylS := by
  have hYeq : (Y.subgroupOf Qj).map Qj.subtype = Y := Subgroup.map_subgroupOf_eq_of_le hYQ
  calc Y.map (MulAut.conj (g : MulAut ↥Jc)).toMonoidHom
      = ((Y.subgroupOf Qj).map Qj.subtype).map
          (MulAut.conj (g : MulAut ↥Jc)).toMonoidHom := by rw [hYeq]
    _ = (Y.subgroupOf Qj).map
          ((MulAut.conj (g : MulAut ↥Jc)).toMonoidHom.comp Qj.subtype) := by
          rw [Subgroup.map_map]
    _ ≤ P.map ((MulAut.conj (g : MulAut ↥Jc)).toMonoidHom.comp Qj.subtype) :=
          Subgroup.map_mono hY'P
    _ = (P.map (MulAut.conj g).toMonoidHom).map Qj.subtype := by
          rw [Subgroup.map_map]
          rfl
    _ = ((g • P : Sylow 2 Qj) : Subgroup Qj).map Qj.subtype := by
          rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
          rfl
    _ = sylS := by
          rw [hg]
          exact Subgroup.map_subgroupOf_eq_of_le sylS_le_Qj

theorem noOffenders_Qj (Y : Subgroup (MulAut ↥Jc)) (hYQ : Y ≤ Qj)
    (hY : IsElementaryAbelian 2 Y) (hY1 : Y ≠ ⊥) :
    Nat.card Y * Nat.card {a : ↥Jc // ∀ y ∈ Y, y a = a} < 2 ^ 10 := by
  haveI : IsElementaryAbelian 2 Y := hY
  haveI hY'elem : IsElementaryAbelian 2 (Y.subgroupOf Qj) := IsElementaryAbelian.subgroupOf hYQ
  have hY'p : IsPGroup 2 (Y.subgroupOf Qj) := IsElementaryAbelian.isPGroup 2 _
  obtain ⟨P, hY'P⟩ := IsPGroup.exists_le_sylow hY'p
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Qj) P sylSylow
  let Z : Subgroup (MulAut ↥Jc) := Y.map (MulAut.conj (g : MulAut ↥Jc)).toMonoidHom
  have hZS : Z ≤ sylS := map_conj_le_sylS hYQ hY'P hg
  haveI hZ : IsElementaryAbelian 2 Z := IsElementaryAbelian.map _
  have hZ1 : Z ≠ ⊥ := by
    intro hbot
    apply hY1
    rw [eq_bot_iff]
    intro y hy
    have hmem : (MulAut.conj (g : MulAut ↥Jc)) y ∈ Z := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    rw [hbot] at hmem
    have h1 : (MulAut.conj (g : MulAut ↥Jc)) y = 1 := by simpa using hmem
    have h2 : ((MulAut.conj (g : MulAut ↥Jc))⁻¹) ((MulAut.conj (g : MulAut ↥Jc)) y) = 1 := by
      rw [h1, map_one]
    rwa [MulAut.inv_apply_self] at h2
  have hbound := card_mul_fixed_le hZS hZ hZ1
  have hcardZ : Nat.card Z = Nat.card Y := Subgroup.card_map_of_injective
    (MulAut.conj (g : MulAut ↥Jc)).injective
  have hfixZ : Nat.card {a : ↥Jc // ∀ z ∈ Z, z a = a} =
      Nat.card {a : ↥Jc // ∀ y ∈ Y, y a = a} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun a => ⟨((g : MulAut ↥Jc)⁻¹) a.1, ?_⟩
        invFun := fun a => ⟨(g : MulAut ↥Jc) a.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro y hy
      have hzy : (MulAut.conj (g : MulAut ↥Jc)) y ∈ Z := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      have hfix := a.2 _ hzy
      have hval : (MulAut.conj (g : MulAut ↥Jc)) y a.1 =
          (g : MulAut ↥Jc) (y (((g : MulAut ↥Jc)⁻¹) a.1)) := rfl
      rw [hval] at hfix
      have := congrArg (fun x => ((g : MulAut ↥Jc)⁻¹) x) hfix
      simpa using this
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      change ((MulAut.conj (g : MulAut ↥Jc)) y) ((g : MulAut ↥Jc) a.1) = (g : MulAut ↥Jc) a.1
      have hval : ((MulAut.conj (g : MulAut ↥Jc)) y) ((g : MulAut ↥Jc) a.1) =
          (g : MulAut ↥Jc) (y (((g : MulAut ↥Jc)⁻¹) ((g : MulAut ↥Jc) a.1))) := rfl
      rw [hval, MulAut.inv_apply_self, a.2 y hy]
    · intro a
      apply Subtype.ext
      change (g : MulAut ↥Jc) (((g : MulAut ↥Jc)⁻¹) a.1) = a.1
      exact MulAut.apply_inv_self (M := ↥Jc) (g : MulAut ↥Jc) a.1
    · intro a
      apply Subtype.ext
      change ((g : MulAut ↥Jc)⁻¹) ((g : MulAut ↥Jc) a.1) = a.1
      exact MulAut.inv_apply_self (M := ↥Jc) (g : MulAut ↥Jc) a.1
  rw [hcardZ, hfixZ] at hbound
  have h1024 : (2 : ℕ) ^ 10 = 1024 := by norm_num
  omega

end CFSG.Sporadic.Co2Jc
