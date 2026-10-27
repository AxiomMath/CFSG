module

public import CFSG.Sporadic.Recognition.LyonsAmalgamTrInputs
public import CFSG.Sporadic.Recognition.LyonsAmalgamEnum
public import CFSG.Sporadic.Recognition.LyonsAmalgamLines

public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly243

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem deg_lt : deg < 2 ^ 32 := by norm_num [deg]

@[expose] noncomputable def gg (i : ℕ) : Perm (Fin deg) := tp deg genTabs[i]!

@[expose] noncomputable def k0 : Perm (Fin deg) := gg 4

@[expose] noncomputable def lineG (i : ℕ) : Perm (Fin deg) := tp deg lineTabs[i]!

@[expose] noncomputable def a3 : Fin 3 → Perm (Fin deg) := fun i => lineG i

noncomputable abbrev Tr0 : Subgroup (Perm (Fin deg)) := genOf deg genTabs.toList

noncomputable abbrev Tx0 : Subgroup (Perm (Fin deg)) := genOf deg (genTabs.toList.take 4)

@[expose] noncomputable def trLetG (l : ℤ) : Perm (Fin deg) :=
  if 0 < l then gg (l.toNat - 1) else (gg ((-l).toNat - 1))⁻¹

@[expose] noncomputable def txyG (j : ℕ) : Perm (Fin deg) := wordG trLetG txyWords[j]!

noncomputable abbrev Txy0 : Subgroup (Perm (Fin deg)) := genOf deg txyTabs.toList

@[expose] noncomputable def txyLetG (l : ℤ) : Perm (Fin deg) :=
  if 0 < l then txyG (l.toNat - 1) else (txyG ((-l).toNat - 1))⁻¹

@[expose] noncomputable def repG (i : ℕ) : Perm (Fin deg) := wordG trLetG repWords[i]!

section Facts

variable (h : trCheck = true)
include h

theorem trCheck_parts : tablesOK = true ∧ permutesOK = true ∧ fixZeroOK = true ∧
    kSwapOK = true ∧ txyKerOK = true ∧ txyEnumOK = true ∧ txyCenterOK = true ∧ cosetOK = true ∧
    kCompatOK = true := by
  simp only [trCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem tablesOK_parts : genTabs.size = 5 ∧ lineTabs.size = 3 ∧ txyTabs.size = 5 ∧
    repTabs.size = 6 ∧ wordsOK = true ∧
    (∀ T ∈ genTabs.toList ++ lineTabs.toList ++ txyTabs.toList ++ repTabs.toList,
      permOK deg T = true ∧ invOK deg T (invT deg T) = true) ∧ lineDataOK = true := by
  have := (trCheck_parts h).1
  simp only [tablesOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at this
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, hw⟩, hp⟩, hl⟩ := this
  exact ⟨ha, hb, hc, hd, hw, fun T hT => by simpa [Bool.and_eq_true] using hp T hT, hl⟩

theorem trTables_perm : ∀ T ∈ genTabs.toList ++ lineTabs.toList ++ txyTabs.toList ++
    repTabs.toList, permOK deg T = true ∧ invOK deg T (invT deg T) = true :=
  (tablesOK_parts h).2.2.2.2.2.1

theorem gen_mem {i : ℕ} (hi : i < 5) : genTabs[i]! ∈ genTabs.toList ++ lineTabs.toList ++
    txyTabs.toList ++ repTabs.toList := by
  have hsz := (tablesOK_parts h).1
  rw [List.mem_append, List.mem_append, List.mem_append]
  left; left; left
  rw [getElem!_pos genTabs i (by omega)]
  exact Array.getElem_mem_toList _

theorem line_mem {i : ℕ} (hi : i < 3) : lineTabs[i]! ∈ genTabs.toList ++ lineTabs.toList ++
    txyTabs.toList ++ repTabs.toList := by
  have hsz := (tablesOK_parts h).2.1
  rw [List.mem_append, List.mem_append, List.mem_append]
  left; left; right
  rw [getElem!_pos lineTabs i (by omega)]
  exact Array.getElem_mem_toList _

theorem rep_gg {i : ℕ} (hi : i < 5) : Rep deg genTabs[i]! (gg i) :=
  rep_tp (trTables_perm h _ (gen_mem h hi)).1

theorem rep_ggInv {i : ℕ} (hi : i < 5) : Rep deg (invT deg genTabs[i]!) (gg i)⁻¹ :=
  rep_invT (rep_gg h hi) (trTables_perm h _ (gen_mem h hi)).2

theorem rep_lineG {i : ℕ} (hi : i < 3) : Rep deg lineTabs[i]! (lineG i) :=
  rep_tp (trTables_perm h _ (line_mem h hi)).1

theorem rep_lineInv {i : ℕ} (hi : i < 3) : Rep deg (invT deg lineTabs[i]!) (lineG i)⁻¹ :=
  rep_invT (rep_lineG h hi) (trTables_perm h _ (line_mem h hi)).2

theorem genInvTabs_get {i : ℕ} (hi : i < 5) : genInvTabs[i]! = invT deg genTabs[i]! := by
  have hsz := (tablesOK_parts h).1
  unfold genInvTabs
  rw [getElem!_pos (genTabs.map (invT deg)) i (by simp; omega), Array.getElem_map,
    getElem!_pos genTabs i (by omega)]

theorem lineInvTabs_get {i : ℕ} (hi : i < 3) : lineInvTabs[i]! = invT deg lineTabs[i]! := by
  have hsz := (tablesOK_parts h).2.1
  unfold lineInvTabs
  rw [getElem!_pos (lineTabs.map (invT deg)) i (by simp; omega), Array.getElem_map,
    getElem!_pos lineTabs i (by omega)]

theorem rep_ggInv' {i : ℕ} (hi : i < 5) : Rep deg genInvTabs[i]! (gg i)⁻¹ := by
  rw [genInvTabs_get h hi]; exact rep_ggInv h hi

theorem rep_lineInv' {i : ℕ} (hi : i < 3) : Rep deg lineInvTabs[i]! (lineG i)⁻¹ := by
  rw [lineInvTabs_get h hi]; exact rep_lineInv h hi

theorem rep_trLet {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 5) : Rep deg (trLet l) (trLetG l) := by
  unfold trLet trLetG
  split_ifs with hpos
  · exact rep_gg h (by omega)
  · exact rep_ggInv' h (by omega)

theorem rep_wordT_tr {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 5) :
    Rep deg (wordT deg trLet w) (wordG trLetG w) :=
  Rep.wordT deg_lt w fun l hl => rep_trLet h (hw l hl)

theorem words_range_tr : (∀ w ∈ txyWords, ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 4) ∧
    (∀ w ∈ repWords, ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 5) ∧
    (∀ w ∈ CFSG.Sporadic.Recognition.LyonsSims.Ly1080.sigmaTxyWords, ∀ l ∈ w,
      l ≠ 0 ∧ l.natAbs ≤ 5) := by
  have hw := (tablesOK_parts h).2.2.2.2.1
  simp only [wordsOK, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hw
  exact ⟨hw.1.1, hw.1.2, hw.2⟩

omit h in
theorem inLine_iff {z a ai : Table} {zg ag : Perm (Fin deg)} (hz : Rep deg z zg)
    (ha : Rep deg a ag) (hai : Rep deg ai ag⁻¹) :
    inLine z a ai = true ↔ zg = ag ∨ zg = ag⁻¹ := by
  rw [inLine, Bool.or_eq_true, tblEq_iff_eq hz ha, tblEq_iff_eq hz hai]

theorem lineDataOK_parts : (∀ i < 3, ordTest deg 3 lineTabs[i]! = true) ∧
    (∀ i < 3, ∀ j < 3, i ≠ j → inLine lineTabs[j]! lineTabs[i]! lineInvTabs[i]! = false) := by
  have := (tablesOK_parts h).2.2.2.2.2.2
  simp only [lineDataOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true'] at this
  refine ⟨this.1, fun i hi j hj hij => ?_⟩
  rcases this.2 i hi j hj with h1 | h1
  · exact absurd h1 hij
  · exact h1

theorem orderOf_lineG {i : ℕ} (hi : i < 3) : orderOf (lineG i) = 3 :=
  (ordTest_iff_perm (rep_lineG h hi) (by norm_num)).1 ((lineDataOK_parts h).1 i hi)

theorem lineData_a3 : LineData a3 where
  pow_three i := by
    show lineG i ^ 3 = 1
    exact orderOf_dvd_iff_pow_eq_one.1 (by rw [orderOf_lineG h i.2])
  ne_one i := by
    intro h1
    have := orderOf_lineG h (i := i) i.2
    have h1' : lineG i = 1 := h1
    rw [h1', orderOf_one] at this
    omega
  not_mem i j hji := by
    have hp3 : (a3 i) ^ 3 = 1 := by
      show (lineG i) ^ 3 = 1
      exact orderOf_dvd_iff_pow_eq_one.1 (by rw [orderOf_lineG h i.2])
    intro hm
    have hij : (i : ℕ) ≠ j := fun e => hji (Fin.ext e.symm)
    have hf := (lineDataOK_parts h).2 i i.2 j j.2 hij
    have hjo := orderOf_lineG h (i := j) j.2
    rcases mem_zpowers_cases hp3 hm with e | e | e
    · have e' : lineG j = 1 := e
      rw [e', orderOf_one] at hjo
      omega
    · have := (inLine_iff (rep_lineG h j.2) (rep_lineG h i.2) (rep_lineInv' h i.2)).2 (Or.inl e)
      rw [hf] at this
      exact Bool.false_ne_true this
    · have := (inLine_iff (rep_lineG h j.2) (rep_lineG h i.2) (rep_lineInv' h i.2)).2 (Or.inr e)
      rw [hf] at this
      exact Bool.false_ne_true this

theorem repConj_gen_line {m i : ℕ} (hm : m < 5) (hi : i < 3) :
    Rep deg (conjA genTabs[m]! genInvTabs[m]! lineTabs[i]!) (gg m * lineG i * (gg m)⁻¹) :=
  rep_conjT (rep_gg h hm) (rep_ggInv' h hm) (rep_lineG h hi)

theorem gg_permutes {m : ℕ} (hm : m < 5) : ∃ σ : Perm (Fin 3), LinePerm a3 (gg m) σ := by
  have hperm := (trCheck_parts h).2.1
  simp only [permutesOK, List.all_eq_true, List.mem_range, List.any_eq_true] at hperm
  refine (lineData_a3 h).exists_linePerm fun i => ?_
  obtain ⟨j, hj, hjt⟩ := hperm m hm i i.2
  refine ⟨⟨j, hj⟩, ?_⟩
  have := (inLine_iff (repConj_gen_line h hm i.2) (rep_lineG h hj) (rep_lineInv' h hj)).1 hjt
  rcases this with e | e
  · show gg m * lineG i * (gg m)⁻¹ ∈ zpowers (lineG j)
    rw [e]; exact mem_zpowers _
  · show gg m * lineG i * (gg m)⁻¹ ∈ zpowers (lineG j)
    rw [e]; exact inv_mem (mem_zpowers _)

theorem gg_mem_Tr0 {i : ℕ} (hi : i < 5) : gg i ∈ Tr0 := by
  have := tp_mem_genOf (n := deg) (gs := genTabs.toList) (g := genTabs[i]!) (by
    have hsz := (tablesOK_parts h).1
    rw [getElem!_pos genTabs i (by omega)]
    exact Array.getElem_mem_toList _)
  exact this

theorem Tr0_le_permuting : Tr0 ≤ permutingLines a3 (lineData_a3 h) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨T, hT, rfl⟩
  have hT' : T ∈ genTabs := by simpa using hT
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hT'
  have hsz := (tablesOK_parts h).1
  have e : tp deg genTabs[i] = gg i := congrArg (tp deg) (getElem!_pos genTabs i hi).symm
  exact Eq.mpr (congrArg (· ∈ permutingLines a3 (lineData_a3 h)) e)
    (gg_permutes h (by omega))

@[expose] noncomputable def trHom : ↥Tr0 →* Perm (Fin 3) :=
  (lineHom a3 (lineData_a3 h)).comp (Subgroup.inclusion (Tr0_le_permuting h))

theorem trHom_spec (n : ↥Tr0) : LinePerm a3 (n : Perm (Fin deg)) (trHom h n) :=
  lineHom_spec (lineData_a3 h) (Subgroup.inclusion (Tr0_le_permuting h) n)

theorem trHom_eq_of_linePerm (n : ↥Tr0) {σ : Perm (Fin 3)}
    (hn : LinePerm a3 (n : Perm (Fin deg)) σ) : trHom h n = σ :=
  (lineData_a3 h).linePerm_unique (trHom_spec h n) hn

theorem txyWords_length : txyWords.length = 5 := by
  have := (tablesOK_parts h).2.2.1
  simpa [txyTabs] using this

theorem txyWords_get_mem {j : ℕ} (hj : j < 5) : txyWords[j]! ∈ txyWords := by
  rw [getElem!_pos txyWords j (by have := txyWords_length h; omega)]
  exact List.getElem_mem _

theorem txyTabs_get {j : ℕ} (hj : j < 5) : txyTabs[j]! = wordT deg trLet txyWords[j]! := by
  have hl := txyWords_length h
  unfold txyTabs
  rw [getElem!_pos (txyWords.toArray.map (wordT deg trLet)) j (by simp; omega), Array.getElem_map,
    getElem!_pos txyWords j (by omega)]
  simp

theorem txyTabs_mem {j : ℕ} (hj : j < 5) : txyTabs[j]! ∈ genTabs.toList ++ lineTabs.toList ++
    txyTabs.toList ++ repTabs.toList := by
  have hsz := (tablesOK_parts h).2.2.1
  rw [List.mem_append, List.mem_append, List.mem_append]
  left; right
  rw [getElem!_pos txyTabs j (by omega)]
  exact Array.getElem_mem_toList _

theorem rep_txyTab {j : ℕ} (hj : j < 5) : Rep deg txyTabs[j]! (txyG j) := by
  rw [txyTabs_get h hj]
  have hr := (words_range_tr h).1 _ (txyWords_get_mem h hj)
  exact rep_wordT_tr h fun l hl => ⟨(hr l hl).1, by have := (hr l hl).2; omega⟩

theorem tp_txyTab {j : ℕ} (hj : j < 5) : tp deg txyTabs[j]! = txyG j :=
  rep_unique (rep_tp (trTables_perm h _ (txyTabs_mem h hj)).1) (rep_txyTab h hj)

theorem txyInvTabs_get {j : ℕ} (hj : j < 5) : txyInvTabs[j]! = invT deg txyTabs[j]! := by
  have hsz := (tablesOK_parts h).2.2.1
  unfold txyInvTabs
  rw [getElem!_pos (txyTabs.map (invT deg)) j (by simp; omega), Array.getElem_map,
    getElem!_pos txyTabs j (by omega)]

theorem rep_txyInvTab {j : ℕ} (hj : j < 5) : Rep deg txyInvTabs[j]! (txyG j)⁻¹ := by
  rw [txyInvTabs_get h hj]
  exact rep_invT (rep_txyTab h hj) (trTables_perm h _ (txyTabs_mem h hj)).2

theorem rep_txyLet {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 5) : Rep deg (txyLet l) (txyLetG l) := by
  unfold txyLet txyLetG
  split_ifs with hpos
  · exact rep_txyTab h (by omega)
  · exact rep_txyInvTab h (by omega)

theorem rep_wordT_txy {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 5) :
    Rep deg (wordT deg txyLet w) (wordG txyLetG w) :=
  Rep.wordT deg_lt w fun l hl => rep_txyLet h (hw l hl)

theorem txyG_mem_Txy0 {j : ℕ} (hj : j < 5) : txyG j ∈ Txy0 := by
  have := tp_mem_genOf (n := deg) (gs := txyTabs.toList) (g := txyTabs[j]!) (by
    have hsz := (tablesOK_parts h).2.2.1
    rw [getElem!_pos txyTabs j (by omega)]
    exact Array.getElem_mem_toList _)
  rwa [tp_txyTab h hj] at this

theorem Txy0_gens {T : Table} (hT : T ∈ txyTabs) : ∃ j, j < 5 ∧ tp deg T = txyG j := by
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hT
  have hsz := (tablesOK_parts h).2.2.1
  refine ⟨j, by omega, ?_⟩
  have := tp_txyTab h (j := j) (by omega)
  rwa [getElem!_pos txyTabs j hj] at this

theorem gg_mem_Tx0 {i : ℕ} (hi : i < 4) : gg i ∈ Tx0 := by
  have hsz := (tablesOK_parts h).1
  refine tp_mem_genOf (n := deg) (gs := genTabs.toList.take 4) (g := genTabs[i]!) ?_
  rw [getElem!_pos genTabs i (by omega), List.mem_take_iff_getElem]
  exact ⟨i, by simp [Array.length_toList, hsz]; omega, by simp⟩

theorem trLetG_mem_Tx0 {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 4) : trLetG l ∈ Tx0 := by
  unfold trLetG
  split_ifs with hpos
  · exact gg_mem_Tx0 h (by omega)
  · exact inv_mem (gg_mem_Tx0 h (by omega))

theorem txyG_mem_Tx0 {j : ℕ} (hj : j < 5) : txyG j ∈ Tx0 := by
  have hr := (words_range_tr h).1 _ (txyWords_get_mem h hj)
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact trLetG_mem_Tx0 h (hr l hl)

omit h in
theorem Tx0_le_Tr0 : Tx0 ≤ Tr0 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨T, hT, rfl⟩
  have hT' : T ∈ genTabs.toList.take 4 := by simpa using hT
  exact subset_closure ⟨T, by simpa using List.mem_of_mem_take hT', rfl⟩

theorem Txy0_le_Tx0 : Txy0 ≤ Tx0 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨T, hT, rfl⟩
  have hT' : T ∈ txyTabs := by simpa using hT
  obtain ⟨j, hj, e⟩ := Txy0_gens h hT'
  exact Eq.mpr (congrArg (· ∈ Tx0) e) (txyG_mem_Tx0 h hj)

theorem Tx0_fix_zero : ∀ x ∈ Tx0, ∃ σ : Perm (Fin 3), LinePerm a3 x σ ∧ σ 0 = 0 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨T, hT, rfl⟩ := hy
    have hT' : T ∈ genTabs.toList.take 4 := by simpa using hT
    rw [List.mem_take_iff_getElem] at hT'
    obtain ⟨i, hi, rfl⟩ := hT'
    have hsz := (tablesOK_parts h).1
    have hi5 : i < 5 := by simp at hi; omega
    have hi4 : i < 4 := by simp at hi; exact hi.1
    have e : tp deg genTabs.toList[i] = gg i := by
      have : genTabs.toList[i] = genTabs[i]! := by
        rw [getElem!_pos genTabs i (by omega)]; exact Array.getElem_toList _
      rw [this]; rfl
    obtain ⟨σ, hσ⟩ := gg_permutes h hi5
    refine ⟨σ, Eq.mpr (congrArg (fun z => LinePerm a3 z σ) e) hσ, ?_⟩
    have hfix := (trCheck_parts h).2.2.1
    simp only [fixZeroOK, List.all_eq_true, List.mem_range] at hfix
    have h1 := (inLine_iff (repConj_gen_line h hi5 (by norm_num : 0 < 3))
      (rep_lineG h (by norm_num)) (rep_lineInv' h (by norm_num))).1 (hfix i hi4)
    have h2 : gg i * a3 0 * (gg i)⁻¹ ∈ zpowers (a3 0) := by
      show gg i * lineG 0 * (gg i)⁻¹ ∈ zpowers (lineG 0)
      rcases h1 with e1 | e1
      · rw [e1]; exact mem_zpowers _
      · rw [e1]; exact inv_mem (mem_zpowers _)
    exact (lineData_a3 h).eq_of_mem ((lineData_a3 h).conj_ne_one (gg i) 0) (hσ 0) h2
  | one => exact ⟨1, LinePerm.one, rfl⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨σ, hσ, h0⟩ := ihx
    obtain ⟨τ, hτ, h1⟩ := ihy
    exact ⟨σ * τ, hσ.mul hτ, by simp [h0, h1]⟩
  | inv x hx ih =>
    obtain ⟨σ, hσ, h0⟩ := ih
    exact ⟨σ⁻¹, (lineData_a3 h).linePerm_inv hσ, by
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]; exact h0.symm⟩

theorem trHom_fix_zero (x : ↥Tr0) (hx : (x : Perm (Fin deg)) ∈ Tx0) : trHom h x 0 = 0 := by
  obtain ⟨σ, hσ, h0⟩ := Tx0_fix_zero h x hx
  rw [trHom_eq_of_linePerm h x hσ]
  exact h0

theorem Txy0_linePerm_one : ∀ x ∈ Txy0, LinePerm a3 x 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨T, hT, rfl⟩ := hy
    have hT' : T ∈ txyTabs := by simpa using hT
    obtain ⟨j, hj, e⟩ := Txy0_gens h hT'
    have hker := (trCheck_parts h).2.2.2.2.1
    simp only [txyKerOK, List.all_eq_true, List.mem_range] at hker
    have hrj := rep_txyTab h hj
    have hrji := rep_txyInvTab h hj
    refine Eq.mpr (congrArg (fun z => LinePerm a3 z 1) e) fun i => ?_
    have h1 := (inLine_iff (rep_conjT hrj hrji (rep_lineG h i.2)) (rep_lineG h i.2)
      (rep_lineInv' h i.2)).1 (hker j hj i i.2)
    show txyG j * lineG i * (txyG j)⁻¹ ∈ zpowers (a3 ((1 : Perm (Fin 3)) i))
    rw [Equiv.Perm.one_apply]
    show txyG j * lineG i * (txyG j)⁻¹ ∈ zpowers (lineG i)
    rcases h1 with e1 | e1
    · rw [e1]; exact mem_zpowers _
    · rw [e1]; exact inv_mem (mem_zpowers _)
  | one => exact LinePerm.one
  | mul x y hx hy ihx ihy => simpa using ihx.mul ihy
  | inv x hx ih => simpa using (lineData_a3 h).linePerm_inv ih

theorem k0_mem : k0 ∈ Tr0 := gg_mem_Tr0 h (by norm_num : 4 < 5)

theorem linePerm_k0 : LinePerm a3 k0 (swap 0 1) := by
  have hk := (trCheck_parts h).2.2.2.1
  simp only [kSwapOK, Bool.and_eq_true] at hk
  obtain ⟨⟨hk0, hk1⟩, hk2⟩ := hk
  have h40 : (4 : ℕ) < 5 := by norm_num
  have e : (swap (0 : Fin 3) 1) 0 = 1 ∧ (swap (0 : Fin 3) 1) 1 = 0 ∧
      (swap (0 : Fin 3) 1) 2 = 2 := by
    decide
  intro i
  fin_cases i
  · show gg 4 * lineG 0 * (gg 4)⁻¹ ∈ zpowers (a3 ((swap (0 : Fin 3) 1) 0))
    rw [e.1]
    have := (inLine_iff (repConj_gen_line h h40 (by norm_num : 0 < 3))
      (rep_lineG h (by norm_num : 1 < 3)) (rep_lineInv' h (by norm_num : 1 < 3))).1 hk0
    show gg 4 * lineG 0 * (gg 4)⁻¹ ∈ zpowers (lineG 1)
    rcases this with e1 | e1
    · rw [e1]; exact mem_zpowers _
    · rw [e1]; exact inv_mem (mem_zpowers _)
  · show gg 4 * lineG 1 * (gg 4)⁻¹ ∈ zpowers (a3 ((swap (0 : Fin 3) 1) 1))
    rw [e.2.1]
    have := (inLine_iff (repConj_gen_line h h40 (by norm_num : 1 < 3))
      (rep_lineG h (by norm_num : 0 < 3)) (rep_lineInv' h (by norm_num : 0 < 3))).1 hk1
    show gg 4 * lineG 1 * (gg 4)⁻¹ ∈ zpowers (lineG 0)
    rcases this with e1 | e1
    · rw [e1]; exact mem_zpowers _
    · rw [e1]; exact inv_mem (mem_zpowers _)
  · show gg 4 * lineG 2 * (gg 4)⁻¹ ∈ zpowers (a3 ((swap (0 : Fin 3) 1) 2))
    rw [e.2.2]
    have := (inLine_iff (repConj_gen_line h h40 (by norm_num : 2 < 3))
      (rep_lineG h (by norm_num : 2 < 3)) (rep_lineInv' h (by norm_num : 2 < 3))).1 hk2
    show gg 4 * lineG 2 * (gg 4)⁻¹ ∈ zpowers (lineG 2)
    rcases this with e1 | e1
    · rw [e1]; exact mem_zpowers _
    · rw [e1]; exact inv_mem (mem_zpowers _)

theorem trHom_k0 : trHom h ⟨k0, k0_mem h⟩ = swap 0 1 :=
  trHom_eq_of_linePerm h _ (linePerm_k0 h)

theorem exactEnum_txy : ExactEnum deg Txy0 txyEnum.1 :=
  (ExactEnum.of_enumOK deg_lt (fun g hg => (trTables_perm h g (by
    rw [List.mem_append, List.mem_append, List.mem_append]; left; right; exact hg)).1)
    (trCheck_parts h).2.2.2.2.2.1).2

theorem memT_mem_Txy0 {z : Table} {zg : Perm (Fin deg)} (hz : Rep deg z zg)
    (hm : memT deg txyEnum.1 z = true) : zg ∈ Txy0 := by
  have hE := exactEnum_txy h
  obtain ⟨k, hk, e⟩ := memT_spec (fun k hk => hE.rep k hk) hz hm
  rw [e]
  exact hE.mem k hk

theorem repWords_length : repWords.length = 6 := by
  have := (tablesOK_parts h).2.2.2.1
  simpa [repTabs] using this

theorem repWords_get_mem {j : ℕ} (hj : j < 6) : repWords[j]! ∈ repWords := by
  rw [getElem!_pos repWords j (by have := repWords_length h; omega)]
  exact List.getElem_mem _

theorem repTabs_get {j : ℕ} (hj : j < 6) : repTabs[j]! = wordT deg trLet repWords[j]! := by
  have hl := repWords_length h
  unfold repTabs
  rw [getElem!_pos (repWords.toArray.map (wordT deg trLet)) j (by simp; omega), Array.getElem_map,
    getElem!_pos repWords j (by omega)]
  simp

theorem repTabs_mem {j : ℕ} (hj : j < 6) : repTabs[j]! ∈ genTabs.toList ++ lineTabs.toList ++
    txyTabs.toList ++ repTabs.toList := by
  have hsz := (tablesOK_parts h).2.2.2.1
  rw [List.mem_append]
  right
  rw [getElem!_pos repTabs j (by omega)]
  exact Array.getElem_mem_toList _

theorem rep_repTab {j : ℕ} (hj : j < 6) : Rep deg repTabs[j]! (repG j) := by
  rw [repTabs_get h hj]
  have hr := (words_range_tr h).2.1 _ (repWords_get_mem h hj)
  exact rep_wordT_tr h hr

theorem rep_repInv {j : ℕ} (hj : j < 6) : Rep deg (invT deg repTabs[j]!) (repG j)⁻¹ :=
  rep_invT (rep_repTab h hj) (trTables_perm h _ (repTabs_mem h hj)).2

theorem repG_zero : repG 0 = 1 := by
  have hc := (trCheck_parts h).2.2.2.2.2.2.2.1
  simp only [cosetOK, Bool.and_eq_true] at hc
  exact (tblEq_iff_eq (rep_repTab h (by norm_num : 0 < 6)) (Rep.idT deg_lt)).1 hc.1.1

theorem coset_cover : ∀ x ∈ Tr0, ∃ j, j < 6 ∧ x * (repG j)⁻¹ ∈ Txy0 := by
  have hc := (trCheck_parts h).2.2.2.2.2.2.2.1
  simp only [cosetOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at hc
  have step : ∀ i < 6, ∀ g : Table, ∀ gg' : Perm (Fin deg), Rep deg g gg' →
      g ∈ genTabs.toList ++ genInvTabs.toList → ∃ j, j < 6 ∧ repG i * gg' * (repG j)⁻¹ ∈ Txy0 := by
    intro i hi g gg' hg hmem
    obtain ⟨j, hj, hm⟩ := hc.1.2 i hi g hmem
    exact ⟨j, hj, memT_mem_Txy0 h (Rep.compT (Rep.compT (rep_repTab h hi) hg)
      (rep_repInv h hj)) hm⟩
  intro x hx
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨0, by norm_num, by rw [repG_zero h]; simp⟩
  | mul_right x hx y hy ih =>
    obtain ⟨i, hi, hxi⟩ := ih
    obtain ⟨T, hT, rfl⟩ := hy
    have hT' : T ∈ genTabs := by simpa using hT
    obtain ⟨m, hm, rfl⟩ := Array.getElem_of_mem hT'
    have hsz := (tablesOK_parts h).1
    have e : tp deg genTabs[m] = gg m := congrArg (tp deg) (getElem!_pos genTabs m hm).symm
    obtain ⟨j, hj, hjt⟩ := step i hi genTabs[m] (gg m) (by
      have := rep_gg h (i := m) (by omega)
      rwa [getElem!_pos genTabs m hm] at this) (by
      rw [List.mem_append]; left; exact Array.getElem_mem_toList _)
    refine ⟨j, hj, ?_⟩
    rw [e]
    have : x * gg m * (repG j)⁻¹ = (x * (repG i)⁻¹) * (repG i * gg m * (repG j)⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hxi hjt
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨i, hi, hxi⟩ := ih
    obtain ⟨T, hT, rfl⟩ := hy
    have hT' : T ∈ genTabs := by simpa using hT
    obtain ⟨m, hm, rfl⟩ := Array.getElem_of_mem hT'
    have hsz := (tablesOK_parts h).1
    have e : tp deg genTabs[m] = gg m := congrArg (tp deg) (getElem!_pos genTabs m hm).symm
    obtain ⟨j, hj, hjt⟩ := step i hi genInvTabs[m]! (gg m)⁻¹ (rep_ggInv' h (by omega)) (by
      rw [List.mem_append]; right
      rw [getElem!_pos genInvTabs m (by simp [genInvTabs]; omega)]
      exact Array.getElem_mem_toList _)
    refine ⟨j, hj, ?_⟩
    rw [e]
    have : x * (gg m)⁻¹ * (repG j)⁻¹ = (x * (repG i)⁻¹) * (repG i * (gg m)⁻¹ * (repG j)⁻¹) := by
      group
    rw [this]
    exact Subgroup.mul_mem _ hxi hjt

theorem repG_not_fixes {j : ℕ} (hj : j < 6) (hj0 : j ≠ 0) : ¬ LinePerm a3 (repG j) 1 := by
  intro hlp
  have hc := (trCheck_parts h).2.2.2.2.2.2.2.1
  simp only [cosetOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  have h3 := hc.2 j hj
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h3
  rcases h3 with e | e
  · exact hj0 e
  · have hall : fixesLines repTabs[j]! = true := by
      simp only [fixesLines, List.all_eq_true, List.mem_range]
      intro i hi
      have hrc := rep_conjT (rep_repTab h hj) (rep_repInv h hj) (rep_lineG h hi)
      refine (inLine_iff hrc (rep_lineG h hi) (rep_lineInv' h hi)).2 ?_
      have h1 := hlp ⟨i, hi⟩
      have h1' : repG j * lineG i * (repG j)⁻¹ ∈ zpowers (lineG i) := by simpa [a3] using h1
      rcases (lineData_a3 h).cases ⟨i, hi⟩ h1' with e1 | e1 | e1
      · exact absurd e1 ((lineData_a3 h).conj_ne_one (repG j) ⟨i, hi⟩)
      · exact Or.inl e1
      · exact Or.inr e1
    rw [hall] at e
    exact absurd e (by decide)

theorem ker_trHom (n : ↥Tr0) : trHom h n = 1 ↔ (n : Perm (Fin deg)) ∈ Txy0 := by
  constructor
  · intro hn
    obtain ⟨j, hj, hm⟩ := coset_cover h n n.2
    by_cases hj0 : j = 0
    · subst hj0
      rwa [repG_zero h, inv_one, mul_one] at hm
    · exfalso
      refine repG_not_fixes h hj hj0 ?_
      have h1 := Txy0_linePerm_one h _ hm
      have h2 : LinePerm a3 (n : Perm (Fin deg)) 1 := by
        have := trHom_spec h n
        rwa [hn] at this
      have := (lineData_a3 h).linePerm_inv h1
      have h3 := this.mul h2
      have e : (↑n * (repG j)⁻¹)⁻¹ * (n : Perm (Fin deg)) = repG j := by group
      simpa [e] using h3
  · intro hn
    exact trHom_eq_of_linePerm h n (Txy0_linePerm_one h _ hn)

theorem txyG_mem_Tr0 {j : ℕ} (hj : j < 5) : txyG j ∈ Tr0 :=
  Tx0_le_Tr0 (txyG_mem_Tx0 h hj)

theorem center_ker_trHom : center (trHom h).ker = ⊥ := by
  have hE := exactEnum_txy h
  have hctr := (trCheck_parts h).2.2.2.2.2.2.1
  simp only [txyCenterOK] at hctr
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Subtype.ext
  show ((z : ↥Tr0) : Perm (Fin deg)) = 1
  have hzT : ((z : ↥Tr0) : Perm (Fin deg)) ∈ Txy0 := (ker_trHom h _).1 z.2
  have hc : ∀ j, (hj : j < 5) → txyG j * ((z : ↥Tr0) : Perm (Fin deg)) =
      ((z : ↥Tr0) : Perm (Fin deg)) * txyG j := fun j hj => by
    have := Subgroup.mem_center_iff.1 hz
      ⟨⟨txyG j, txyG_mem_Tr0 h hj⟩, (ker_trHom h _).2 (txyG_mem_Txy0 h hj)⟩
    exact congrArg (fun w : ↥(trHom h).ker => ((w : ↥Tr0) : Perm (Fin deg))) this
  obtain ⟨k, hk, hrep⟩ := hE.cover _ hzT
  have h1 := Array.all_eq_true.1 hctr k hk
  rw [getElem!_pos txyEnum.1 k hk] at hrep
  have hall : (txyTabs.all fun g => commTT deg txyEnum.1[k] g) = true := by
    rw [Array.all_eq_true]
    intro j hj
    have hsz := (tablesOK_parts h).2.2.1
    have hrj := rep_txyTab h (j := j) (by omega)
    rw [getElem!_pos txyTabs j hj] at hrj
    exact (commTT_iff hrep hrj).2 (hc j (by omega)).symm
  rw [hall] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  exact (tblEq_iff_eq hrep (Rep.idT deg_lt)).1 h1

theorem k0_conj_txyG {j : ℕ} (hj : j < 5) :
    k0 * txyG j * k0⁻¹ = wordG txyLetG
      CFSG.Sporadic.Recognition.LyonsSims.Ly1080.sigmaTxyWords[j]! := by
  have hk := (trCheck_parts h).2.2.2.2.2.2.2.2
  simp only [kCompatOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hk
  have hmem : CFSG.Sporadic.Recognition.LyonsSims.Ly1080.sigmaTxyWords[j]! ∈
      CFSG.Sporadic.Recognition.LyonsSims.Ly1080.sigmaTxyWords := by
    rw [getElem!_pos _ j (by omega)]
    exact List.getElem_mem _
  have h1 := rep_conjT (rep_gg h (by norm_num : 4 < 5)) (rep_ggInv' h (by norm_num : 4 < 5))
    (rep_txyTab h hj)
  have hr := (words_range_tr h).2.2 _ hmem
  exact (tblEq_iff_eq h1 (rep_wordT_txy h hr)).1 (hk.2 j hj)

theorem wordG_txyLetG_mem {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 5) :
    wordG txyLetG w ∈ Txy0 :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hl0, hl5⟩ := hw l hl
    unfold txyLetG
    split_ifs with hpos
    · exact txyG_mem_Txy0 h (by omega)
    · exact inv_mem (txyG_mem_Txy0 h (by omega))

end Facts

end CFSG.Sporadic.Recognition.LyonsSims.Ly243
