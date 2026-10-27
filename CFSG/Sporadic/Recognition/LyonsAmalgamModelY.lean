module

public import CFSG.Sporadic.Recognition.LyonsAmalgamYInputs
public import CFSG.Sporadic.Recognition.LyonsAmalgamEnum

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly1080

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem deg_lt : deg < 2 ^ 32 := by norm_num [deg]

@[expose] noncomputable def ug (i : ℕ) : Perm (Fin deg) := tp deg uTabs[i]!

@[expose] noncomputable def sigma0 : Perm (Fin deg) := tp deg sigmaTab

noncomputable abbrev Y0 : Subgroup (Perm (Fin deg)) := genOf deg uTabs.toList

section Tables

variable (h : tablesOK = true)
include h

theorem tablesOK_sizes : uTabs.size = 4 ∧ txyTabs.size = 5 := by
  simp only [tablesOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1

theorem tablesOK_perm : ∀ T ∈ uTabs.toList ++ [sigmaTab] ++ txyTabs.toList,
    permOK deg T = true ∧ invOK deg T (invT deg T) = true := by
  simp only [tablesOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  intro T hT
  exact h.1.2 T hT

theorem tablesOK_sq : tblEq deg (compT deg sigmaTab sigmaTab) (idT deg) = true := by
  simp only [tablesOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem tablesOK_words : wordsOK = true := by
  simp only [tablesOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

theorem rep_u {i : ℕ} (hi : i < 4) : Rep deg uTabs[i]! (ug i) := by
  have hsz := (tablesOK_sizes h).1
  refine rep_tp (tablesOK_perm h _ ?_).1
  rw [List.mem_append, List.mem_append]
  left; left
  rw [getElem!_pos uTabs i (by omega)]
  exact Array.getElem_mem_toList _

theorem rep_uInv {i : ℕ} (hi : i < 4) : Rep deg (invT deg uTabs[i]!) (ug i)⁻¹ := by
  have hsz := (tablesOK_sizes h).1
  refine rep_invT (rep_u h hi) (tablesOK_perm h _ ?_).2
  rw [List.mem_append, List.mem_append]
  left; left
  rw [getElem!_pos uTabs i (by omega)]
  exact Array.getElem_mem_toList _

theorem rep_sigma : Rep deg sigmaTab sigma0 := by
  refine rep_tp (tablesOK_perm h _ ?_).1
  simp

end Tables

@[expose] noncomputable def letG (l : ℤ) : Perm (Fin deg) :=
  if 0 < l then ug (l.toNat - 1) else (ug ((-l).toNat - 1))⁻¹

@[expose] noncomputable def abLetG (l : ℤ) : Perm (Fin deg) :=
  if l = 1 then ug 0 else if l = 2 then ug 3 else if l = -1 then (ug 0)⁻¹ else (ug 3)⁻¹

@[expose] noncomputable def txyG (j : ℕ) : Perm (Fin deg) := wordG letG txyWords[j]!

noncomputable abbrev Txy0 : Subgroup (Perm (Fin deg)) := genOf deg txyTabs.toList

@[expose] noncomputable def txyLetG (l : ℤ) : Perm (Fin deg) :=
  if 0 < l then txyG (l.toNat - 1) else (txyG ((-l).toNat - 1))⁻¹

theorem card_Txy0_of (ht : tablesOK = true) (he : txyEnumOK = true) : Nat.card Txy0 = 3888 :=
  (ExactEnum.of_enumOK deg_lt (fun g hg => (tablesOK_perm ht g (by
    rw [List.mem_append]; right; exact hg)).1) he).1

@[expose] def YOK : Prop :=
  tablesOK = true ∧ erelOK = true ∧ genOK = true ∧ txyEnumOK = true ∧ sigmaTxyOK = true ∧
    center ↥Y0 = ⊥ ∧
    (∀ t ∈ Txy0, ¬ ∀ i < 4, t * ug i * t⁻¹ = sigma0 * ug i * sigma0⁻¹) ∧
    (Nat.card Y0 ≤ 349920 →
      (∀ n ∈ Y0, (∀ t ∈ Txy0, n * t * n⁻¹ ∈ Txy0) → n ∈ Txy0) ∧ Nat.card (MulAut ↥Y0) ≤ 699840)

section Facts

variable (h : YOK)
include h

theorem yCheck_parts : tablesOK = true ∧ erelOK = true ∧ genOK = true ∧ txyEnumOK = true ∧
    sigmaTxyOK = true :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem yCheck_tables : tablesOK = true := (yCheck_parts h).1

theorem sigma_mul_self : sigma0 * sigma0 = 1 := by
  have ht := yCheck_tables h
  have hs := rep_sigma ht
  exact (tblEq_iff_eq (Rep.compT hs hs) (Rep.idT deg_lt)).1 (tablesOK_sq ht)

theorem sigma_inv : sigma0⁻¹ = sigma0 := inv_eq_of_mul_eq_one_right (sigma_mul_self h)

theorem rep_sigma_inv : Rep deg sigmaTab sigma0⁻¹ := by
  rw [sigma_inv h]
  exact rep_sigma (yCheck_tables h)

theorem rep_uLet {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 4) : Rep deg (uLet l) (letG l) := by
  have ht := yCheck_tables h
  have hsz := (tablesOK_sizes ht).1
  unfold uLet letG
  split_ifs with hpos
  · exact rep_u ht (by omega)
  · have hi : (-l).toNat - 1 < 4 := by omega
    have := rep_uInv ht hi
    have hget : uInvTabs[(-l).toNat - 1]! = invT deg uTabs[(-l).toNat - 1]! := by
      unfold uInvTabs
      rw [getElem!_pos (uTabs.map (invT deg)) _ (by simp; omega), Array.getElem_map,
        getElem!_pos uTabs _ (by omega)]
    rw [hget]
    exact this

theorem rep_wordT_u {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 4) :
    Rep deg (wordT deg uLet w) (wordG letG w) :=
  Rep.wordT deg_lt w fun l hl => rep_uLet h (hw l hl)

theorem words_range₄ : ∀ w ∈ erelWords ++ txyWords, ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 4 := by
  have hw := tablesOK_words (yCheck_tables h)
  simp only [wordsOK, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    at hw
  intro w hw' l hl
  exact hw.1.1 w hw' l hl

theorem words_range₂ : ∀ w ∈ genWords ++ autRelators ++ autWitnesses, ∀ l ∈ w,
    l ≠ 0 ∧ l.natAbs ≤ 2 := by
  have hw := tablesOK_words (yCheck_tables h)
  simp only [wordsOK, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    at hw
  intro w hw' l hl
  exact hw.1.2 w hw' l hl

theorem words_range₅ : ∀ w ∈ sigmaTxyWords, ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 5 := by
  have hw := tablesOK_words (yCheck_tables h)
  simp only [wordsOK, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    at hw
  intro w hw' l hl
  exact hw.2 w hw' l hl

theorem sigma_conj_ug {i : ℕ} (hi : i < 4) :
    sigma0 * ug i * sigma0⁻¹ = wordG letG erelWords[i]! := by
  have ht := yCheck_tables h
  have herel := (yCheck_parts h).2.1
  simp only [erelOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_range] at herel
  have hmem : erelWords[i]! ∈ erelWords := by
    rw [getElem!_pos erelWords i (by omega)]
    exact List.getElem_mem _
  have hw := fun l hl => words_range₄ h _ (List.mem_append_left _ hmem) l hl
  have h1 := rep_conjT (rep_sigma ht) (rep_sigma_inv h) (rep_u ht hi)
  exact (tblEq_iff_eq h1 (rep_wordT_u h hw)).1 (herel.2 i hi)

theorem ug_mem {i : ℕ} (hi : i < 4) : ug i ∈ Y0 := by
  have hsz := (tablesOK_sizes (yCheck_tables h)).1
  refine tp_mem_genOf ?_
  rw [getElem!_pos uTabs i (by omega)]
  exact Array.getElem_mem_toList _

theorem letG_mem {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 4) : letG l ∈ Y0 := by
  unfold letG
  split_ifs with hpos
  · exact ug_mem h (by omega)
  · exact inv_mem (ug_mem h (by omega))

theorem wordG_mem_Y0 {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 4) : wordG letG w ∈ Y0 :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact letG_mem h (hw l hl)

theorem rep_abLet {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 2) : Rep deg (abLet l) (abLetG l) := by
  have ht := yCheck_tables h
  have hsz := (tablesOK_sizes ht).1
  have hget : ∀ i : ℕ, i < 4 → uInvTabs[i]! = invT deg uTabs[i]! := fun i hi => by
    unfold uInvTabs
    rw [getElem!_pos (uTabs.map (invT deg)) _ (by simp; omega), Array.getElem_map,
      getElem!_pos uTabs _ (by omega)]
  have hl2 : l = 1 ∨ l = 2 ∨ l = -1 ∨ l = -2 := by omega
  unfold abLet abLetG
  rcases hl2 with rfl | rfl | rfl | rfl
  · simpa using rep_u ht (i := 0) (by norm_num)
  · simpa using rep_u ht (i := 3) (by norm_num)
  · simpa [hget 0 (by norm_num)] using rep_uInv ht (i := 0) (by norm_num)
  · simpa [hget 3 (by norm_num)] using rep_uInv ht (i := 3) (by norm_num)

theorem rep_wordT_ab {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) :
    Rep deg (wordT deg abLet w) (wordG abLetG w) :=
  Rep.wordT deg_lt w fun l hl => rep_abLet h (hw l hl)

theorem Y0_eq_ab : Y0 = genOf deg abTabs.toList := by
  have ht := yCheck_tables h
  have hsz := (tablesOK_sizes ht).1
  have hgen := (yCheck_parts h).2.2.1
  simp only [genOK, Bool.and_eq_true, beq_iff_eq] at hgen
  obtain ⟨⟨hglen, hg1⟩, hg2⟩ := hgen
  set Hab := genOf deg abTabs.toList with hHab
  have hab0 : ug 0 ∈ Hab := by
    refine tp_mem_genOf (g := uTabs[0]!) ?_
    simp [abTabs]
  have hab3 : ug 3 ∈ Hab := by
    refine tp_mem_genOf (g := uTabs[3]!) ?_
    simp [abTabs]
  have hletab : ∀ l : ℤ, (l ≠ 0 ∧ l.natAbs ≤ 2) → abLetG l ∈ Hab := by
    intro l hl
    unfold abLetG
    have hl2 : l = 1 ∨ l = 2 ∨ l = -1 ∨ l = -2 := by omega
    rcases hl2 with rfl | rfl | rfl | rfl
    · simpa using hab0
    · simpa using hab3
    · simpa using inv_mem hab0
    · simpa using inv_mem hab3
  have hwab : ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) → wordG abLetG w ∈ Hab :=
    fun w hw => Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      exact hletab l (hw l hl)
  have hmem : ∀ k, k < 2 → genWords[k]! ∈ genWords := fun k hk => by
    rw [getElem!_pos genWords k (by omega)]
    exact List.getElem_mem _
  have hr := fun w hw => words_range₂ h w (List.mem_append_left _ (List.mem_append_left _ hw))
  have hu1 : ug 1 = wordG abLetG genWords[0]! :=
    (tblEq_iff_eq (rep_u ht (i := 1) (by norm_num))
      (rep_wordT_ab h (hr _ (hmem 0 (by norm_num))))).1 hg1
  have hu2 : ug 2 = wordG abLetG genWords[1]! :=
    (tblEq_iff_eq (rep_u ht (i := 2) (by norm_num))
      (rep_wordT_ab h (hr _ (hmem 1 (by norm_num))))).1 hg2
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨T, hT, rfl⟩
    have hT' : T ∈ uTabs := by simpa using hT
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hT'
    have hi4 : i < 4 := by omega
    have this : tp deg uTabs[i] = ug i := congrArg (tp deg) (getElem!_pos uTabs i hi).symm
    have key : ug i ∈ Hab := by
      interval_cases i
      · exact hab0
      · rw [hu1]; exact hwab _ (hr _ (hmem 0 (by norm_num)))
      · rw [hu2]; exact hwab _ (hr _ (hmem 1 (by norm_num)))
      · exact hab3
    exact Eq.mpr (congrArg (· ∈ Hab) this) key
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨T, hT, rfl⟩
    have hT' : T ∈ abTabs.toList := by simpa using hT
    have hlist : abTabs.toList = [uTabs[0]!, uTabs[3]!] := rfl
    rw [hlist, List.mem_cons, List.mem_singleton] at hT'
    rcases hT' with hT' | hT'
    · rw [hT']; exact ug_mem h (by norm_num : 0 < 4)
    · rw [hT']; exact ug_mem h (by norm_num : 3 < 4)

theorem txyWords_length : txyWords.length = 5 := by
  have := (tablesOK_sizes (yCheck_tables h)).2
  simpa [txyTabs] using this

theorem txyWords_get_mem {j : ℕ} (hj : j < 5) : txyWords[j]! ∈ txyWords := by
  rw [getElem!_pos txyWords j (by have := txyWords_length h; omega)]
  exact List.getElem_mem _

theorem txyTabs_get {j : ℕ} (hj : j < 5) : txyTabs[j]! = wordT deg uLet txyWords[j]! := by
  have hl := txyWords_length h
  unfold txyTabs
  rw [getElem!_pos (txyWords.toArray.map (wordT deg uLet)) j (by simp; omega), Array.getElem_map,
    getElem!_pos txyWords j (by omega)]
  simp

theorem txyTabs_mem {j : ℕ} (hj : j < 5) : txyTabs[j]! ∈ uTabs.toList ++ [sigmaTab] ++
    txyTabs.toList := by
  have hsz := (tablesOK_sizes (yCheck_tables h)).2
  rw [List.mem_append]
  right
  rw [getElem!_pos txyTabs j (by omega)]
  exact Array.getElem_mem_toList _

theorem rep_txyTab {j : ℕ} (hj : j < 5) : Rep deg txyTabs[j]! (txyG j) := by
  rw [txyTabs_get h hj]
  exact rep_wordT_u h fun l hl => words_range₄ h _ (List.mem_append_right _ (txyWords_get_mem h hj))
    l hl

theorem tp_txyTab {j : ℕ} (hj : j < 5) : tp deg txyTabs[j]! = txyG j :=
  rep_unique (rep_tp (tablesOK_perm (yCheck_tables h) _ (txyTabs_mem h hj)).1) (rep_txyTab h hj)

theorem txyInvTabs_get {j : ℕ} (hj : j < 5) : txyInvTabs[j]! = invT deg txyTabs[j]! := by
  have hsz := (tablesOK_sizes (yCheck_tables h)).2
  unfold txyInvTabs
  rw [getElem!_pos (txyTabs.map (invT deg)) j (by simp; omega), Array.getElem_map,
    getElem!_pos txyTabs j (by omega)]

theorem rep_txyInvTab {j : ℕ} (hj : j < 5) : Rep deg txyInvTabs[j]! (txyG j)⁻¹ := by
  rw [txyInvTabs_get h hj]
  exact rep_invT (rep_txyTab h hj) (tablesOK_perm (yCheck_tables h) _ (txyTabs_mem h hj)).2

theorem rep_txyLet {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 5) : Rep deg (txyLet l) (txyLetG l) := by
  unfold txyLet txyLetG
  split_ifs with hpos
  · exact rep_txyTab h (by omega)
  · exact rep_txyInvTab h (by omega)

theorem rep_wordT_txy {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 5) :
    Rep deg (wordT deg txyLet w) (wordG txyLetG w) :=
  Rep.wordT deg_lt w fun l hl => rep_txyLet h (hw l hl)

theorem txyG_mem {j : ℕ} (hj : j < 5) : txyG j ∈ Y0 :=
  wordG_mem_Y0 h fun l hl => words_range₄ h _ (List.mem_append_right _ (txyWords_get_mem h hj)) l hl

theorem txyG_mem_Txy0 {j : ℕ} (hj : j < 5) : txyG j ∈ Txy0 := by
  have := tp_mem_genOf (n := deg) (gs := txyTabs.toList) (g := txyTabs[j]!) (by
    have hsz := (tablesOK_sizes (yCheck_tables h)).2
    rw [getElem!_pos txyTabs j (by omega)]
    exact Array.getElem_mem_toList _)
  rwa [tp_txyTab h hj] at this

theorem Txy0_le_Y0 : Txy0 ≤ Y0 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨T, hT, rfl⟩
  have hT' : T ∈ txyTabs := by simpa using hT
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hT'
  have hsz := (tablesOK_sizes (yCheck_tables h)).2
  have e : tp deg txyTabs[j] = txyG j := by
    have := tp_txyTab h (j := j) (by omega)
    rwa [getElem!_pos txyTabs j hj] at this
  exact Eq.mpr (congrArg (· ∈ Y0) e) (txyG_mem h (by omega))

theorem card_Txy0 : Nat.card Txy0 = 3888 :=
  card_Txy0_of (yCheck_tables h) (yCheck_parts h).2.2.2.1

theorem wordG_mem_Txy0 {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 5) :
    wordG txyLetG w ∈ Txy0 :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hl0, hl5⟩ := hw l hl
    unfold txyLetG
    split_ifs with hpos
    · exact txyG_mem_Txy0 h (by omega)
    · exact inv_mem (txyG_mem_Txy0 h (by omega))

theorem sigma_conj_txyG {j : ℕ} (hj : j < 5) :
    sigma0 * txyG j * sigma0⁻¹ = wordG txyLetG sigmaTxyWords[j]! := by
  have ht := yCheck_tables h
  have hs := (yCheck_parts h).2.2.2.2
  simp only [sigmaTxyOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hs
  have hmem : sigmaTxyWords[j]! ∈ sigmaTxyWords := by
    rw [getElem!_pos sigmaTxyWords j (by omega)]
    exact List.getElem_mem _
  have h1 := rep_conjT (rep_sigma ht) (rep_sigma_inv h) (rep_txyTab h hj)
  exact (tblEq_iff_eq h1 (rep_wordT_txy h fun l hl => words_range₅ h _ hmem l hl)).1 (hs.2 j hj)

theorem sigma_conj_Txy0 : ∀ t ∈ Txy0, sigma0 * t * sigma0⁻¹ ∈ Txy0 := by
  intro t ht
  induction ht using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    have hT' : T ∈ txyTabs := by simpa using hT
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hT'
    have hsz := (tablesOK_sizes (yCheck_tables h)).2
    have e : tp deg txyTabs[j] = txyG j := by
      have := tp_txyTab h (j := j) (by omega)
      rwa [getElem!_pos txyTabs j hj] at this
    rw [e, sigma_conj_txyG h (by omega)]
    have hmem : sigmaTxyWords[j]! ∈ sigmaTxyWords := by
      have hs := (yCheck_parts h).2.2.2.2
      simp only [sigmaTxyOK, Bool.and_eq_true, beq_iff_eq] at hs
      rw [getElem!_pos sigmaTxyWords j (by omega)]
      exact List.getElem_mem _
    exact wordG_mem_Txy0 h fun l hl => words_range₅ h _ hmem l hl
  | one => simp
  | mul x y hx hy ihx ihy =>
    have : sigma0 * (x * y) * sigma0⁻¹ = (sigma0 * x * sigma0⁻¹) * (sigma0 * y * sigma0⁻¹) := by
      group
    rw [this]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ihx =>
    have : sigma0 * x⁻¹ * sigma0⁻¹ = (sigma0 * x * sigma0⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ihx

omit h in
theorem abTabs_get₀ : abTabs[0]! = uTabs[0]! := by simp [abTabs]

omit h in
theorem abTabs_get₁ : abTabs[1]! = uTabs[3]! := by simp [abTabs]

theorem rep_ab₀ : Rep deg abTabs[0]! (ug 0) := by
  rw [abTabs_get₀]; exact rep_u (yCheck_tables h) (by norm_num)

theorem rep_ab₁ : Rep deg abTabs[1]! (ug 3) := by
  rw [abTabs_get₁]; exact rep_u (yCheck_tables h) (by norm_num)

theorem exactEnum_txy : ExactEnum deg Txy0 txyEnum.1 :=
  (ExactEnum.of_enumOK deg_lt (fun g hg => (tablesOK_perm (yCheck_tables h) g (by
    rw [List.mem_append]; right; exact hg)).1) (yCheck_parts h).2.2.2.1).2

theorem center_Y0 : center ↥Y0 = ⊥ := h.2.2.2.2.2.1

theorem normalizer_Txy0 (hcard : Nat.card Y0 ≤ 349920) :
    ∀ n ∈ Y0, (∀ t ∈ Txy0, n * t * n⁻¹ ∈ Txy0) → n ∈ Txy0 :=
  (h.2.2.2.2.2.2.2 hcard).1

theorem card_mulAut_Y0 (hcard : Nat.card Y0 ≤ 349920) : Nat.card (MulAut ↥Y0) ≤ 699840 :=
  (h.2.2.2.2.2.2.2 hcard).2

theorem not_inner_Txy0 : ∀ t ∈ Txy0, ¬ ∀ i < 4, t * ug i * t⁻¹ = sigma0 * ug i * sigma0⁻¹ :=
  h.2.2.2.2.2.2.1

theorem sigma_conj_mem_Y0 : ∀ y ∈ Y0, sigma0 * y * sigma0⁻¹ ∈ Y0 := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    have hT' : T ∈ uTabs := by simpa using hT
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hT'
    have hsz := (tablesOK_sizes (yCheck_tables h)).1
    have e : tp deg uTabs[i] = ug i := congrArg (tp deg) (getElem!_pos uTabs i hi).symm
    have key : sigma0 * ug i * sigma0⁻¹ ∈ Y0 := by
      have hi4 : i < 4 := by omega
      rw [sigma_conj_ug h hi4]
      have hmem : erelWords[i]! ∈ erelWords := by
        have herel := (yCheck_parts h).2.1
        simp only [erelOK, Bool.and_eq_true, beq_iff_eq] at herel
        rw [getElem!_pos erelWords i (by omega)]
        exact List.getElem_mem _
      exact wordG_mem_Y0 h fun l hl => words_range₄ h _ (List.mem_append_left _ hmem) l hl
    exact Eq.mpr (congrArg (fun z => sigma0 * z * sigma0⁻¹ ∈ Y0) e) key
  | one => simp
  | mul x y hx hy ihx ihy =>
    have : sigma0 * (x * y) * sigma0⁻¹ = (sigma0 * x * sigma0⁻¹) * (sigma0 * y * sigma0⁻¹) := by
      group
    rw [this]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ihx =>
    have : sigma0 * x⁻¹ * sigma0⁻¹ = (sigma0 * x * sigma0⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ihx

end Facts

@[expose] noncomputable def kappa0 (h : YOK) : MulAut ↥Y0 where
  toFun y := ⟨sigma0 * y * sigma0⁻¹, sigma_conj_mem_Y0 h y y.2⟩
  invFun y := ⟨sigma0 * y * sigma0⁻¹, sigma_conj_mem_Y0 h y y.2⟩
  left_inv y := by
    apply Subtype.ext
    have hs : sigma0 * sigma0 = 1 := sigma_mul_self h
    have hs' : sigma0⁻¹ = sigma0 := sigma_inv h
    show sigma0 * (sigma0 * (y : Perm (Fin deg)) * sigma0⁻¹) * sigma0⁻¹ = y
    rw [hs']
    calc sigma0 * (sigma0 * (y : Perm (Fin deg)) * sigma0) * sigma0
        = (sigma0 * sigma0) * y * (sigma0 * sigma0) := by group
      _ = y := by rw [hs]; group
  right_inv y := by
    apply Subtype.ext
    have hs : sigma0 * sigma0 = 1 := sigma_mul_self h
    have hs' : sigma0⁻¹ = sigma0 := sigma_inv h
    show sigma0 * (sigma0 * (y : Perm (Fin deg)) * sigma0⁻¹) * sigma0⁻¹ = y
    rw [hs']
    calc sigma0 * (sigma0 * (y : Perm (Fin deg)) * sigma0) * sigma0
        = (sigma0 * sigma0) * y * (sigma0 * sigma0) := by group
      _ = y := by rw [hs]; group
  map_mul' x y := by
    apply Subtype.ext
    show sigma0 * ((x : Perm (Fin deg)) * y) * sigma0⁻¹ =
      sigma0 * (x : Perm (Fin deg)) * sigma0⁻¹ * (sigma0 * (y : Perm (Fin deg)) * sigma0⁻¹)
    group

theorem kappa0_coe (h : YOK) (y : ↥Y0) :
    ((kappa0 h y : ↥Y0) : Perm (Fin deg)) = sigma0 * y * sigma0⁻¹ := rfl


end CFSG.Sporadic.Recognition.LyonsSims.Ly1080
