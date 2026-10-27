module

public import CFSG.Sporadic.Recognition.LyonsAmalgamGlue
public import CFSG.Sporadic.Recognition.LyonsAmalgamGlueModel
public import CFSG.Sporadic.Recognition.LyonsModelStage

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Glue

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Recognition.LyonsSims

@[expose] noncomputable def txG (k : ℕ) : Perm (Fin Ly0.deg) :=
  Ly0.wG Ly0.gens0 (txWords.getD k [])

@[expose] noncomputable def txyBp (j : ℕ) : Perm (Fin Ly0.deg) :=
  wordG (wordLetter Ly0.uG) Ly1080.txyWords[j]!

theorem txWords_length : txWords.length = 4 := rfl

theorem txB_size : txB.size = 4 := by simp [txB, txWords_length]

theorem txWords_range : ∀ w ∈ txWords, ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro w hw l hl
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hw
  exact Ly0.decodeWord_mem s l hl

theorem txWords_getD_range {k : ℕ} (hk : k < 4) :
    ∀ l ∈ txWords.getD k [], l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro l hl
  refine txWords_range _ ?_ l hl
  rw [List.getD_eq_getElem _ _ (by rw [txWords_length]; exact hk)]
  exact List.getElem_mem _

theorem txB_get {k : ℕ} (hk : k < 4) :
    txB[k]! = Ly0.wT Ly0.tabs0 Ly0.invs0 (txWords.getD k []) := by
  have hlen : k < txWords.length := by rw [txWords_length]; exact hk
  have hk' : k < (txWords.map (Ly0.wT Ly0.tabs0 Ly0.invs0)).toArray.size := by simpa using hlen
  unfold txB
  rw [getElem!_pos _ k hk', List.getD_eq_getElem _ _ hlen]
  simp

theorem rep_txB (h : Ly0.tabCheck = true) {k : ℕ} (hk : k < 4) : Rep Ly0.deg txB[k]! (txG k) := by
  rw [txB_get hk]
  exact Ly0.rep_word0 h _ (txWords_getD_range hk)

theorem rep_txInvB (h : Ly0.tabCheck = true) {k : ℕ} (hk : k < 4) :
    Rep Ly0.deg txInvB[k]! (txG k)⁻¹ := by
  have : txInvB[k]! = invT Ly0.deg txB[k]! := by
    have hk' : k < txB.size := by rw [txB_size]; exact hk
    unfold txInvB
    rw [getElem!_pos _ k (by simpa using hk'), Array.getElem_map, getElem!_pos txB k hk']
  rw [this]
  exact rep_invT_of_rep Ly0.deg_lt (rep_txB h hk)

theorem rep_txLetB (h : Ly0.tabCheck = true) {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 4) :
    Rep Ly0.deg (txLetB l) (wordLetter txG l) := by
  unfold txLetB wordLetter
  split_ifs with hpos
  · exact rep_txB h (by omega)
  · exact rep_txInvB h (by omega)

theorem rep_uLetB (h : Ly0.tabCheck = true) {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 4) :
    Rep Ly0.deg (uLetB l) (wordLetter Ly0.uG l) := by
  unfold uLetB wordLetter
  split_ifs with hpos
  · exact Ly0.rep_uTabs h (by omega)
  · exact Ly0.rep_uInvTabs h (by omega)

theorem tauOK_parts (h : Tau.tauOK = true) :
    mulTreeOK Ly243.deg Ly243.txyTabs Tau.tEnum Tau.yEnum.2.1 Tau.yEnum.2.2 = true ∧
    hkeysDistinct Ly243.deg Tau.tEnum.toList = true ∧ Tau.tEnum.size = Tau.yEnum.1.size ∧
    ∀ k < Tau.yEnum.1.size, ∀ l < 5,
      ((Tau.succTab[k]!)[l]! < Tau.yEnum.1.size ∧
        tblEq Ly1080.deg Tau.yEnum.1[(Tau.succTab[k]!)[l]!]!
          (compT Ly1080.deg Tau.yEnum.1[k]! Ly1080.txyTabs[l]!) = true) ∧
      tblEq Ly243.deg Tau.tEnum[(Tau.succTab[k]!)[l]!]!
        (compT Ly243.deg Tau.tEnum[k]! Ly243.txyTabs[l]!) = true := by
  simp only [Tau.tauOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨ht₂, hd₂⟩, hsz₂⟩, -⟩, hsucc⟩ := h
  exact ⟨ht₂, hd₂, hsz₂, hsucc⟩

theorem yTree_parts (hY : Ly1080.YOK) :
    mulTreeOK Ly1080.deg Ly1080.txyTabs Tau.yEnum.1 Tau.yEnum.2.1 Tau.yEnum.2.2 = true ∧
    hkeysDistinct Ly1080.deg Tau.yEnum.1.toList = true := by
  have htxy := (Ly1080.yCheck_parts hY).2.2.2.1
  simp only [Ly1080.txyEnumOK, CFSG.Sporadic.SmallOddCore.enumOK, Bool.and_eq_true,
    beq_iff_eq, List.all_eq_true] at htxy
  exact ⟨htxy.1.1.1.2, htxy.1.2⟩

theorem treeB_parts (h : treeBOK = true) :
    mulTreeOK Ly0.deg txyB hEnumB Tau.yEnum.2.1 Tau.yEnum.2.2 = true ∧
    hkeysDistinct Ly0.deg hEnumB.toList = true ∧ hEnumB.size = Tau.yEnum.1.size ∧
    (∀ j < 5, tblEq Ly0.deg txyB[j]! txyBx[j]! = true) ∧
    ∀ k < hEnumB.size, ∀ l < 5, (Tau.succTab[k]!)[l]! < hEnumB.size ∧
      tblEq Ly0.deg hEnumB[(Tau.succTab[k]!)[l]!]! (compT Ly0.deg hEnumB[k]! txyB[l]!) = true := by
  simp only [treeBOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun k hk l hl => ?_⟩
  exact h5 k hk l hl

theorem txyB_size (hY : Ly1080.YOK) : txyB.size = 5 := by
  simp [txyB, Ly1080.txyWords_length hY]

theorem txyB_get (hY : Ly1080.YOK) {l : ℕ} (hl : l < 5) :
    txyB[l]! = wordT Ly0.deg uLetB Ly1080.txyWords[l]! := by
  have hlen : l < Ly1080.txyWords.length := by rw [Ly1080.txyWords_length hY]; exact hl
  have hl' : l < (Ly1080.txyWords.toArray.map (wordT Ly0.deg uLetB)).size := by simpa using hlen
  unfold txyB
  rw [getElem!_pos _ l hl', getElem!_pos Ly1080.txyWords l hlen]
  simp

theorem rep_txyB (hM : Ly0.ModelChecks) (hY : Ly1080.YOK) {l : ℕ} (hl : l < 5) :
    Rep Ly0.deg txyB[l]! (txyBp l) := by
  rw [txyB_get hY hl]
  exact Rep.wordT Ly0.deg_lt _ fun l' hl' => rep_uLetB hM.tab
    (Ly1080.words_range₄ hY _ (List.mem_append_right _ (Ly1080.txyWords_get_mem hY hl)) l' hl')

theorem txyBx_size (hT : Ly243.trCheck = true) : txyBx.size = 5 := by
  simp [txyBx, Ly243.txyWords_length hT]

theorem Txy0_le_closure1080 (hY : Ly1080.YOK) :
    Ly1080.Txy0 ≤ Subgroup.closure (Ly1080.txyG '' {l | l < 5}) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨T, hT, rfl⟩
  have hT' : T ∈ Ly1080.txyTabs := by simpa using hT
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hT'
  have hsz := (Ly1080.tablesOK_sizes (Ly1080.yCheck_tables hY)).2
  have e : tp Ly1080.deg Ly1080.txyTabs[j] = Ly1080.txyG j := by
    have := Ly1080.tp_txyTab hY (j := j) (by omega)
    rwa [getElem!_pos Ly1080.txyTabs j hj] at this
  have hj5 : j < 5 := by omega
  rw [e]
  exact Subgroup.subset_closure ⟨j, hj5, rfl⟩

theorem Txy0_le_closure243 (hT : Ly243.trCheck = true) :
    Ly243.Txy0 ≤ Subgroup.closure (Ly243.txyG '' {l | l < 5}) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨T, hT', rfl⟩
  have hT'' : T ∈ Ly243.txyTabs := by simpa using hT'
  obtain ⟨j, hj, e⟩ := Ly243.Txy0_gens hT hT''
  rw [e]
  exact Subgroup.subset_closure ⟨j, hj, rfl⟩

theorem exists_treeIso1080 (hM : Ly0.ModelChecks) (hY : Ly1080.YOK)
    (hτ : Tau.tauOK = true) (hg : treeBOK = true) :
    ExactEnum Ly0.deg (Subgroup.closure (txyBp '' {l | l < 5})) hEnumB ∧
    ∃ ι : ↥(Subgroup.closure (txyBp '' {l | l < 5})) ≃* ↥Ly1080.Txy0,
      (∀ (k : ℕ) (_ : k < hEnumB.size)
        (hmem : tablePerm Ly0.deg hEnumB[k]! ∈ Subgroup.closure (txyBp '' {l | l < 5})),
        ((ι ⟨tablePerm Ly0.deg hEnumB[k]!, hmem⟩ : ↥Ly1080.Txy0) : Perm (Fin Ly1080.deg)) =
          tablePerm Ly1080.deg Tau.yEnum.1[k]!) ∧
      ∀ (l : ℕ) (_ : l < 5) (hmem : txyBp l ∈ Subgroup.closure (txyBp '' {l | l < 5})),
        ((ι ⟨txyBp l, hmem⟩ : ↥Ly1080.Txy0) : Perm (Fin Ly1080.deg)) = Ly1080.txyG l := by
  obtain ⟨hT₁, hd₁, hs, -, hsucc₁⟩ := treeB_parts hg
  obtain ⟨hT₂, hd₂⟩ := yTree_parts hY
  obtain ⟨-, -, -, hsucc₂⟩ := tauOK_parts hτ
  exact exists_treeEquiv Ly0.deg_lt Ly1080.deg_lt (m := 5) (G₁ := txyB) (G₂ := Ly1080.txyTabs)
    (E₁ := hEnumB) (E₂ := Tau.yEnum.1) (par := Tau.yEnum.2.1) (lab := Tau.yEnum.2.2)
    (succ := Tau.succTab) (g₁ := txyBp) (g₂ := Ly1080.txyG) (txyB_size hY)
    ((Ly1080.tablesOK_sizes (Ly1080.yCheck_tables hY)).2) (fun l hl => rep_txyB hM hY hl)
    (fun l hl => Ly1080.rep_txyTab hY hl) hT₁ hT₂ hd₁ hd₂ hs.symm
    (fun k hk l hl => ⟨(hsucc₁ k hk l hl).1, (hsucc₁ k hk l hl).2,
      (hsucc₂ k (hs ▸ hk) l hl).1.2⟩)
    (Txy0_le_closure1080 hY) (fun l hl => Ly1080.txyG_mem_Txy0 hY hl)

theorem exists_treeIso243 (hM : Ly0.ModelChecks) (hY : Ly1080.YOK)
    (hT : Ly243.trCheck = true) (hτ : Tau.tauOK = true) (hg : treeBOK = true) :
    ∃ ι : ↥(Subgroup.closure (txyBp '' {l | l < 5})) ≃* ↥Ly243.Txy0,
      (∀ (k : ℕ) (_ : k < hEnumB.size)
        (hmem : tablePerm Ly0.deg hEnumB[k]! ∈ Subgroup.closure (txyBp '' {l | l < 5})),
        ((ι ⟨tablePerm Ly0.deg hEnumB[k]!, hmem⟩ : ↥Ly243.Txy0) : Perm (Fin Ly243.deg)) =
          tablePerm Ly243.deg Tau.tEnum[k]!) ∧
      ∀ (l : ℕ) (_ : l < 5) (hmem : txyBp l ∈ Subgroup.closure (txyBp '' {l | l < 5})),
        ((ι ⟨txyBp l, hmem⟩ : ↥Ly243.Txy0) : Perm (Fin Ly243.deg)) = Ly243.txyG l := by
  obtain ⟨hT₁, hd₁, hs, -, hsucc₁⟩ := treeB_parts hg
  obtain ⟨hT₂, hd₂, hs₂, hsucc₂⟩ := tauOK_parts hτ
  exact (exists_treeEquiv Ly0.deg_lt Ly243.deg_lt (m := 5) (G₁ := txyB) (G₂ := Ly243.txyTabs)
    (E₁ := hEnumB) (E₂ := Tau.tEnum) (par := Tau.yEnum.2.1) (lab := Tau.yEnum.2.2)
    (succ := Tau.succTab) (g₁ := txyBp) (g₂ := Ly243.txyG) (txyB_size hY)
    ((Ly243.tablesOK_parts hT).2.2.1) (fun l hl => rep_txyB hM hY hl)
    (fun l hl => Ly243.rep_txyTab hT hl) hT₁ hT₂ hd₁ hd₂ (hs₂.trans hs.symm)
    (fun k hk l hl => ⟨(hsucc₁ k hk l hl).1, (hsucc₁ k hk l hl).2,
      (hsucc₂ k (hs ▸ hk) l hl).2⟩)
    (Txy0_le_closure243 hT) (fun l hl => Ly243.txyG_mem_Txy0 hT hl)).2

theorem wordsInRange_spec {ws : Array (List ℤ)} {m : ℕ} (h : wordsInRange ws m = true) :
    ∀ i < ws.size, ∀ l ∈ ws[i]!, l ≠ 0 ∧ l.natAbs ≤ m := by
  intro i hi l hl
  simp only [wordsInRange, Array.all_eq_true, List.all_eq_true, Bool.and_eq_true,
    bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  have := h i hi l (by rwa [getElem!_pos ws i hi] at hl)
  exact this

theorem wordG_mem_closure {A : Type*} [Group A] (g : ℕ → A) (m : ℕ) {w : List ℤ}
    (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m) :
    wordG (wordLetter g) w ∈ Subgroup.closure (g '' {k | k < m}) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons l w ih =>
    have hl := hw l (List.mem_cons_self ..)
    have hw' : ∀ l' ∈ w, l' ≠ 0 ∧ l'.natAbs ≤ m := fun l' hl' =>
      hw l' (List.mem_cons_of_mem _ hl')
    have e : wordG (wordLetter g) (l :: w) = wordLetter g l * wordG (wordLetter g) w := rfl
    rw [e]
    refine Subgroup.mul_mem _ ?_ (ih hw')
    unfold wordLetter
    split_ifs with hpos
    · exact Subgroup.subset_closure ⟨l.toNat - 1, show l.toNat - 1 < m by omega, rfl⟩
    · exact Subgroup.inv_mem _
        (Subgroup.subset_closure ⟨(-l).toNat - 1, show (-l).toNat - 1 < m by omega, rfl⟩)

theorem UYperm_eq : Ly0.UYperm = Subgroup.closure (Ly0.uG '' {k | k < 4}) := by
  have h : Set.range (fun j : Fin 4 => Ly0.uG j.val) = Ly0.uG '' {k | k < 4} := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.val, j.isLt, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  show Subgroup.closure (Set.range (fun j : Fin 4 => Ly0.uG j.val)) = _
  rw [h]

theorem Y0_le_closure1080 (hY : Ly1080.YOK) :
    Ly1080.Y0 ≤ Subgroup.closure (Ly1080.ug '' {k | k < 4}) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨T, hT, rfl⟩
  have hT' : T ∈ Ly1080.uTabs := by simpa using hT
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hT'
  have hsz := (Ly1080.tablesOK_sizes (Ly1080.yCheck_tables hY)).1
  have e : tp Ly1080.deg Ly1080.uTabs[j] = Ly1080.ug j := by
    have := Ly1080.rep_u (Ly1080.yCheck_tables hY) (i := j) (by omega)
    rw [getElem!_pos Ly1080.uTabs j hj] at this
    exact rep_unique (rep_tp (Ly1080.tablesOK_perm (Ly1080.yCheck_tables hY) _
      (by rw [List.mem_append, List.mem_append]; left; left; exact Array.getElem_mem_toList _)).1)
      this
  have hj4 : j < 4 := by omega
  rw [e]
  exact Subgroup.subset_closure ⟨j, hj4, rfl⟩

theorem Tx0_le_closure243 (hT : Ly243.trCheck = true) :
    Ly243.Tx0 ≤ Subgroup.closure (Ly243.gg '' {k | k < 4}) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨T, hT', rfl⟩
  have hT'' : T ∈ Ly243.genTabs.toList.take 4 := by simpa using hT'
  obtain ⟨k, hk, hTk⟩ := List.getElem_of_mem hT''
  have hsz := (Ly243.tablesOK_parts hT).1
  have hk4 : k < 4 := by
    have := hk
    simp only [List.length_take, Array.length_toList] at this
    omega
  have e : tp Ly243.deg T = Ly243.gg k := by
    have h1 := Ly243.rep_gg hT (i := k) (by omega)
    have h2 : T = Ly243.genTabs[k]! := by
      rw [← hTk, getElem!_pos Ly243.genTabs k (by omega)]
      simp
    rw [h2]
    exact rep_unique (rep_tp (Ly243.trTables_perm hT _ (by
      rw [List.mem_append, List.mem_append, List.mem_append]
      left; left; left; rw [getElem!_pos Ly243.genTabs k (by omega)]
      exact Array.getElem_mem_toList _)).1) h1
  rw [e]
  exact Subgroup.subset_closure ⟨k, hk4, rfl⟩

theorem repTables_get (n : Nat) (lt : Int → Table) (ws : Array (List ℤ)) {i : ℕ}
    (hi : i < ws.size) : (repTables n lt ws)[i]! = wordT n lt ws[i]! := by
  have hi' : i < (ws.map (wordT n lt)).size := by simpa using hi
  unfold repTables
  rw [getElem!_pos _ i hi', getElem!_pos ws i hi]
  simp

theorem repTables_size (n : Nat) (lt : Int → Table) (ws : Array (List ℤ)) :
    (repTables n lt ws).size = ws.size := by
  simp [repTables]

theorem yRepsA_size : yRepsA.size = ySearch.1.size := repTables_size _ _ _

theorem yRepsB_size : yRepsB.size = ySearch.1.size := repTables_size _ _ _

theorem xRepsA_size : xRepsA.size = xSearch.1.size := repTables_size _ _ _

theorem xRepsB_size : xRepsB.size = xSearch.1.size := repTables_size _ _ _

theorem yCosetOK_parts (h : yCosetOK = true) :
    wordsInRange ySearch.1 4 = true ∧ ySearch.1.size = 90 ∧
    sideOK Ly1080.deg Ly1080.uTabs yRepsA Tau.yEnum.1 ySearch.2 = true ∧
    sideOK Ly0.deg Ly0.uTabs yRepsB hEnumB ySearch.2 = true := by
  simp only [yCosetOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem xCosetOK_parts (h : xCosetOK = true) :
    wordsInRange xSearch.1 4 = true ∧ xSearch.1.size = 2 ∧
    sideOK Ly243.deg (Ly243.genTabs.extract 0 4) xRepsA Tau.tEnum xSearch.2 = true ∧
    sideOK Ly0.deg txB xRepsB hEnumB xSearch.2 = true := by
  simp only [xCosetOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem rep_yRepsA (hY : Ly1080.YOK) (hr : wordsInRange ySearch.1 4 = true) {i : ℕ}
    (hi : i < ySearch.1.size) :
    Rep Ly1080.deg yRepsA[i]! (wordG Ly1080.letG ySearch.1[i]!) := by
  unfold yRepsA
  rw [repTables_get _ _ _ hi]
  exact Rep.wordT Ly1080.deg_lt _ fun l hl => Ly1080.rep_uLet hY (wordsInRange_spec hr i hi l hl)

theorem rep_yRepsB (hM : Ly0.ModelChecks) (hr : wordsInRange ySearch.1 4 = true) {i : ℕ}
    (hi : i < ySearch.1.size) :
    Rep Ly0.deg yRepsB[i]! (wordG (wordLetter Ly0.uG) ySearch.1[i]!) := by
  unfold yRepsB
  rw [repTables_get _ _ _ hi]
  exact Rep.wordT Ly0.deg_lt _ fun l hl => rep_uLetB hM.tab (wordsInRange_spec hr i hi l hl)

theorem exists_yEquiv (hM : Ly0.ModelChecks) (hY : Ly1080.YOK) (hτ : Tau.tauOK = true)
    (hg : treeBOK = true) (hc : yCosetOK = true) :
    ∃ Φ : ↥Ly0.UYperm ≃* ↥Ly1080.Y0,
      (∀ (k : ℕ) (_ : k < 4) (hmem : Ly0.uG k ∈ Ly0.UYperm),
        ((Φ ⟨Ly0.uG k, hmem⟩ : ↥Ly1080.Y0) : Perm (Fin Ly1080.deg)) = Ly1080.ug k) ∧
      (∀ (x : Perm (Fin Ly0.deg)) (hx : x ∈ Ly0.UYperm),
        x ∈ Subgroup.closure (txyBp '' {l | l < 5}) ↔
          ((Φ ⟨x, hx⟩ : ↥Ly1080.Y0) : Perm (Fin Ly1080.deg)) ∈ Ly1080.Txy0) ∧
      (∀ (l : ℕ) (_ : l < 5) (hmem : txyBp l ∈ Ly0.UYperm),
        ((Φ ⟨txyBp l, hmem⟩ : ↥Ly1080.Y0) : Perm (Fin Ly1080.deg)) = Ly1080.txyG l) ∧
      Nat.card ↥Ly0.UYperm = 349920 := by
  classical
  obtain ⟨hr, hsize, hA, hB⟩ := yCosetOK_parts hc
  obtain ⟨hE₁, ι, hι, hιg⟩ := exists_treeIso1080 hM hY hτ hg
  have hE₂ := Ly1080.exactEnum_txy hY
  have hs := (treeB_parts hg).2.2.1
  have hwr : ∀ i < ySearch.1.size, ∀ l ∈ ySearch.1[i]!, l ≠ 0 ∧ l.natAbs ≤ 4 :=
    wordsInRange_spec hr
  have hHP₁ : Subgroup.closure (txyBp '' {l | l < 5}) ≤ Ly0.UYperm := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨l, hl, rfl⟩
    have hl5 : l < 5 := hl
    unfold txyBp
    rw [UYperm_eq]
    exact wordG_mem_closure Ly0.uG 4 fun l' hl' => Ly1080.words_range₄ hY _
      (List.mem_append_right _ (Ly1080.txyWords_get_mem hY hl5)) l' hl'
  obtain ⟨Φ, hΦH, hΦg, hcard⟩ := exists_cosetEquiv (n₁ := Ly0.deg) (n₂ := Ly1080.deg)
    Ly0.deg_lt Ly1080.deg_lt (m := 4) (G₁ := Ly0.uTabs) (G₂ := Ly1080.uTabs) (V₁ := yRepsB)
    (V₂ := yRepsA) (E₁ := hEnumB) (E₂ := Tau.yEnum.1) (succ := ySearch.2) (g₁ := Ly0.uG)
    (g₂ := Ly1080.ug) (v₁ := fun i => wordG (wordLetter Ly0.uG) ySearch.1[i]!)
    (v₂ := fun i => wordG Ly1080.letG ySearch.1[i]!) (P₁ := Ly0.UYperm)
    (H₁ := Subgroup.closure (txyBp '' {l | l < 5})) (P₂ := Ly1080.Y0) (H₂ := Ly1080.Txy0)
    hHP₁ (Ly1080.Txy0_le_Y0 hY) Ly0.uTabs_size
    ((Ly1080.tablesOK_sizes (Ly1080.yCheck_tables hY)).1)
    (fun k hk => Ly0.rep_uTabs hM.tab hk)
    (fun k hk => Ly1080.rep_u (Ly1080.yCheck_tables hY) hk)
    (fun k hk => Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩) (fun k hk => Ly1080.ug_mem hY hk)
    (UYperm_eq.le) (Y0_le_closure1080 hY)
    (fun i hi => rep_yRepsB hM hr (by rwa [yRepsB_size] at hi))
    (fun i hi => rep_yRepsA hY hr (by rwa [yRepsA_size] at hi))
    (fun i hi => by
      have hi' : i < ySearch.1.size := by rwa [yRepsB_size] at hi
      rw [UYperm_eq]
      exact wordG_mem_closure Ly0.uG 4 (hwr i hi'))
    (fun i hi => by
      have hi' : i < ySearch.1.size := by rwa [yRepsA_size] at hi
      exact Ly1080.wordG_mem_Y0 hY (hwr i hi'))
    (by rw [yRepsA_size, yRepsB_size]) hE₁ hE₂ hs.symm ι hι hB hA
  refine ⟨Φ, fun k hk hmem => hΦg k hk, ?_, ?_, ?_⟩
  · intro x hx
    constructor
    · intro hxH
      have := hΦH x hxH
      show ((Φ ⟨x, hx⟩ : ↥Ly1080.Y0) : Perm (Fin Ly1080.deg)) ∈ Ly1080.Txy0
      rw [this]
      exact (ι ⟨x, hxH⟩).2
    · intro hxT
      let y : ↥(Subgroup.closure (txyBp '' {l | l < 5})) :=
        ι.symm ⟨((Φ ⟨x, hx⟩ : ↥Ly1080.Y0) : Perm (Fin Ly1080.deg)), hxT⟩
      have hy : ((ι y : ↥Ly1080.Txy0) : Perm (Fin Ly1080.deg)) =
          ((Φ ⟨x, hx⟩ : ↥Ly1080.Y0) : Perm (Fin Ly1080.deg)) := by
        have : ι y = ⟨((Φ ⟨x, hx⟩ : ↥Ly1080.Y0) : Perm (Fin Ly1080.deg)), hxT⟩ :=
          ι.apply_symm_apply _
        rw [this]
      have h2 := hΦH (y : Perm (Fin Ly0.deg)) y.2
      have h3 : (Φ ⟨(y : Perm (Fin Ly0.deg)), hHP₁ y.2⟩ : ↥Ly1080.Y0) = Φ ⟨x, hx⟩ :=
        Subtype.ext (h2.trans hy)
      have h4 := Φ.injective h3
      have h5 : (y : Perm (Fin Ly0.deg)) = x := congrArg Subtype.val h4
      rw [← h5]
      exact y.2
  · intro l hl hmem
    have hH : txyBp l ∈ Subgroup.closure (txyBp '' {l | l < 5}) :=
      Subgroup.subset_closure ⟨l, hl, rfl⟩
    have := hΦH (txyBp l) hH
    rw [this]
    exact hιg l hl hH
  · have hHb : Nat.card ↥(Subgroup.closure (txyBp '' {l | l < 5})) = 3888 := by
      rw [Nat.card_congr ι.toEquiv]
      exact Ly1080.card_Txy0 hY
    rw [hcard, yRepsB_size, hsize, hHb]

theorem txyBx_get (hT : Ly243.trCheck = true) {l : ℕ} (hl : l < 5) :
    txyBx[l]! = wordT Ly0.deg txLetB Ly243.txyWords[l]! := by
  have hlen : l < Ly243.txyWords.length := by rw [Ly243.txyWords_length hT]; exact hl
  have hl' : l < (Ly243.txyWords.toArray.map (wordT Ly0.deg txLetB)).size := by simpa using hlen
  unfold txyBx
  rw [getElem!_pos _ l hl', getElem!_pos Ly243.txyWords l hlen]
  simp

theorem rep_txyBx (hM : Ly0.ModelChecks) (hT : Ly243.trCheck = true) {l : ℕ} (hl : l < 5) :
    Rep Ly0.deg txyBx[l]! (wordG (wordLetter txG) Ly243.txyWords[l]!) := by
  rw [txyBx_get hT hl]
  exact Rep.wordT Ly0.deg_lt _ fun l' hl' => rep_txLetB hM.tab
    ((Ly243.words_range_tr hT).1 _ (Ly243.txyWords_get_mem hT hl) l' hl')

theorem txyBp_eq (hM : Ly0.ModelChecks) (hY : Ly1080.YOK) (hT : Ly243.trCheck = true)
    (hg : treeBOK = true) {l : ℕ} (hl : l < 5) :
    txyBp l = wordG (wordLetter txG) Ly243.txyWords[l]! :=
  (tblEq_iff_eq (rep_txyB hM hY hl) (rep_txyBx hM hT hl)).1 ((treeB_parts hg).2.2.2.1 l hl)

theorem rep_xRepsA (hT : Ly243.trCheck = true) (hr : wordsInRange xSearch.1 4 = true) {i : ℕ}
    (hi : i < xSearch.1.size) :
    Rep Ly243.deg xRepsA[i]! (wordG (wordLetter Ly243.gg) xSearch.1[i]!) := by
  unfold xRepsA
  rw [repTables_get _ _ _ hi]
  exact Rep.wordT Ly243.deg_lt _ fun l hl => Ly243.rep_trLet hT
    (by have := wordsInRange_spec hr i hi l hl; exact ⟨this.1, by omega⟩)

theorem rep_xRepsB (hM : Ly0.ModelChecks) (hr : wordsInRange xSearch.1 4 = true) {i : ℕ}
    (hi : i < xSearch.1.size) :
    Rep Ly0.deg xRepsB[i]! (wordG (wordLetter txG) xSearch.1[i]!) := by
  unfold xRepsB
  rw [repTables_get _ _ _ hi]
  exact Rep.wordT Ly0.deg_lt _ fun l hl => rep_txLetB hM.tab (wordsInRange_spec hr i hi l hl)

theorem genTabs_extract_get (hT : Ly243.trCheck = true) {k : ℕ} (hk : k < 4) :
    (Ly243.genTabs.extract 0 4)[k]! = Ly243.genTabs[k]! := by
  have hsz := (Ly243.tablesOK_parts hT).1
  have hk' : k < (Ly243.genTabs.extract 0 4).size := by simp [hsz]; omega
  rw [getElem!_pos _ k hk', getElem!_pos Ly243.genTabs k (by omega)]
  simp

theorem yEnum_size (hY : Ly1080.YOK) : Tau.yEnum.1.size = 3888 := by
  have htxy := (Ly1080.yCheck_parts hY).2.2.2.1
  simp only [Ly1080.txyEnumOK, CFSG.Sporadic.SmallOddCore.enumOK, Bool.and_eq_true,
    beq_iff_eq, List.all_eq_true] at htxy
  exact htxy.2

theorem card_Txy0_243 (hT : Ly243.trCheck = true) : Nat.card Ly243.Txy0 = 3888 :=
  (ExactEnum.of_enumOK Ly243.deg_lt (fun g hg => (Ly243.trTables_perm hT g (by
    rw [List.mem_append, List.mem_append, List.mem_append]; left; right; exact hg)).1)
    (Ly243.trCheck_parts hT).2.2.2.2.2.1).1

theorem exactEnum_tEnum (hY : Ly1080.YOK) (hT : Ly243.trCheck = true)
    (hτ : Tau.tauOK = true) : ExactEnum Ly243.deg Ly243.Txy0 Tau.tEnum := by
  obtain ⟨hT₂, hd₂, hs₂, -⟩ := tauOK_parts hτ
  have hperm : ∀ g ∈ Ly243.txyTabs.toList, permOK Ly243.deg g = true := fun g hg =>
    (Ly243.trTables_perm hT g (by
      rw [List.mem_append, List.mem_append, List.mem_append]; left; right; exact hg)).1
  exact ExactEnum.of_lb Ly243.deg_lt (gs := Ly243.txyTabs.toList) hperm
    (by rw [Array.toArray_toList]; exact hT₂) hd₂ (hs₂.trans (yEnum_size hY))
    (le_of_eq (card_Txy0_243 hT))

theorem exists_xEquiv (hM : Ly0.ModelChecks) (hY : Ly1080.YOK)
    (hT : Ly243.trCheck = true) (hτ : Tau.tauOK = true) (hg : treeBOK = true)
    (hc : xCosetOK = true) :
    ∃ Φ : ↥(Subgroup.closure (txG '' {k | k < 4})) ≃* ↥Ly243.Tx0,
      (∀ (k : ℕ) (_ : k < 4) (hmem : txG k ∈ Subgroup.closure (txG '' {k | k < 4})),
        ((Φ ⟨txG k, hmem⟩ : ↥Ly243.Tx0) : Perm (Fin Ly243.deg)) = Ly243.gg k) ∧
      (∀ (x : Perm (Fin Ly0.deg)) (hx : x ∈ Subgroup.closure (txG '' {k | k < 4})),
        x ∈ Subgroup.closure (txyBp '' {l | l < 5}) ↔
          ((Φ ⟨x, hx⟩ : ↥Ly243.Tx0) : Perm (Fin Ly243.deg)) ∈ Ly243.Txy0) ∧
      (∀ (l : ℕ) (_ : l < 5) (hmem : txyBp l ∈ Subgroup.closure (txG '' {k | k < 4})),
        ((Φ ⟨txyBp l, hmem⟩ : ↥Ly243.Tx0) : Perm (Fin Ly243.deg)) = Ly243.txyG l) ∧
      Nat.card ↥(Subgroup.closure (txG '' {k | k < 4})) = 7776 := by
  classical
  obtain ⟨hr, hsize, hA, hB⟩ := xCosetOK_parts hc
  obtain ⟨hE₁, -, -, -⟩ := exists_treeIso1080 hM hY hτ hg
  obtain ⟨ι, hι, hιg⟩ := exists_treeIso243 hM hY hT hτ hg
  have hE₂ := exactEnum_tEnum hY hT hτ
  have hs := (treeB_parts hg).2.2.1
  have hs₂ := (tauOK_parts hτ).2.2.1
  have hwr : ∀ i < xSearch.1.size, ∀ l ∈ xSearch.1[i]!, l ≠ 0 ∧ l.natAbs ≤ 4 :=
    wordsInRange_spec hr
  have hHP₁ : Subgroup.closure (txyBp '' {l | l < 5}) ≤
      Subgroup.closure (txG '' {k | k < 4}) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨l, hl, rfl⟩
    have hl5 : l < 5 := hl
    rw [txyBp_eq hM hY hT hg hl5]
    exact wordG_mem_closure txG 4 fun l' hl' =>
      (Ly243.words_range_tr hT).1 _ (Ly243.txyWords_get_mem hT hl5) l' hl'
  have hsz4 : (Ly243.genTabs.extract 0 4).size = 4 := by
    have hsz := (Ly243.tablesOK_parts hT).1
    simp [hsz]
  have hTx0 : ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 4) →
      wordG (wordLetter Ly243.gg) w ∈ Ly243.Tx0 := by
    intro w hw
    have := wordG_mem_closure Ly243.gg 4 hw
    refine (Subgroup.closure_le Ly243.Tx0).2 ?_ this
    rintro _ ⟨k, hk, rfl⟩
    exact Ly243.gg_mem_Tx0 hT hk
  obtain ⟨Φ, hΦH, hΦg, hcard⟩ := exists_cosetEquiv (n₁ := Ly0.deg) (n₂ := Ly243.deg)
    Ly0.deg_lt Ly243.deg_lt (m := 4) (G₁ := txB) (G₂ := Ly243.genTabs.extract 0 4)
    (V₁ := xRepsB) (V₂ := xRepsA) (E₁ := hEnumB) (E₂ := Tau.tEnum) (succ := xSearch.2)
    (g₁ := txG) (g₂ := Ly243.gg) (v₁ := fun i => wordG (wordLetter txG) xSearch.1[i]!)
    (v₂ := fun i => wordG (wordLetter Ly243.gg) xSearch.1[i]!)
    (P₁ := Subgroup.closure (txG '' {k | k < 4}))
    (H₁ := Subgroup.closure (txyBp '' {l | l < 5})) (P₂ := Ly243.Tx0) (H₂ := Ly243.Txy0)
    hHP₁ (Ly243.Txy0_le_Tx0 hT) txB_size hsz4
    (fun k hk => rep_txB hM.tab hk)
    (fun k hk => by
      rw [genTabs_extract_get hT hk]
      exact Ly243.rep_gg hT (by omega))
    (fun k hk => Subgroup.subset_closure ⟨k, hk, rfl⟩) (fun k hk => Ly243.gg_mem_Tx0 hT hk)
    le_rfl (Tx0_le_closure243 hT)
    (fun i hi => rep_xRepsB hM hr (by rwa [xRepsB_size] at hi))
    (fun i hi => rep_xRepsA hT hr (by rwa [xRepsA_size] at hi))
    (fun i hi => by
      have hi' : i < xSearch.1.size := by rwa [xRepsB_size] at hi
      exact wordG_mem_closure txG 4 (hwr i hi'))
    (fun i hi => by
      have hi' : i < xSearch.1.size := by rwa [xRepsA_size] at hi
      exact hTx0 _ (hwr i hi'))
    (by rw [xRepsA_size, xRepsB_size]) hE₁ hE₂ (hs₂.trans hs.symm) ι hι hB hA
  refine ⟨Φ, fun k hk hmem => hΦg k hk, ?_, ?_, ?_⟩
  · intro x hx
    constructor
    · intro hxH
      have := hΦH x hxH
      show ((Φ ⟨x, hx⟩ : ↥Ly243.Tx0) : Perm (Fin Ly243.deg)) ∈ Ly243.Txy0
      rw [this]
      exact (ι ⟨x, hxH⟩).2
    · intro hxT
      let y : ↥(Subgroup.closure (txyBp '' {l | l < 5})) :=
        ι.symm ⟨((Φ ⟨x, hx⟩ : ↥Ly243.Tx0) : Perm (Fin Ly243.deg)), hxT⟩
      have hy : ((ι y : ↥Ly243.Txy0) : Perm (Fin Ly243.deg)) =
          ((Φ ⟨x, hx⟩ : ↥Ly243.Tx0) : Perm (Fin Ly243.deg)) := by
        have : ι y = ⟨((Φ ⟨x, hx⟩ : ↥Ly243.Tx0) : Perm (Fin Ly243.deg)), hxT⟩ :=
          ι.apply_symm_apply _
        rw [this]
      have h2 := hΦH (y : Perm (Fin Ly0.deg)) y.2
      have h3 : (Φ ⟨(y : Perm (Fin Ly0.deg)), hHP₁ y.2⟩ : ↥Ly243.Tx0) = Φ ⟨x, hx⟩ :=
        Subtype.ext (h2.trans hy)
      have h4 := Φ.injective h3
      have h5 : (y : Perm (Fin Ly0.deg)) = x := congrArg Subtype.val h4
      rw [← h5]
      exact y.2
  · intro l hl hmem
    have hH : txyBp l ∈ Subgroup.closure (txyBp '' {l | l < 5}) :=
      Subgroup.subset_closure ⟨l, hl, rfl⟩
    have := hΦH (txyBp l) hH
    rw [this]
    exact hιg l hl hH
  · have hHb : Nat.card ↥(Subgroup.closure (txyBp '' {l | l < 5})) = 3888 := by
      rw [Nat.card_congr ι.toEquiv]
      exact card_Txy0_243 hT
    rw [hcard, xRepsB_size, hsize, hHb]

theorem glueCheck_parts (h : glueCheck = true) :
    treeBOK = true ∧ yCosetOK = true ∧ xCosetOK = true ∧ normOK = true := by
  simp only [glueCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem normOK_parts (h : normOK = true) :
    mulTreeOK Ly0.deg #[Ly0.tabX, Ly0.tabYw, Ly0.tabW] a3Enum.1 a3Enum.2.1 a3Enum.2.2 = true ∧
    (∀ j < 5, normLinesOK txyB[j]! (invT Ly0.deg txyB[j]!) = true) ∧
    (∀ k < 4, normA3OK txB[k]! txInvB[k]! = true) := by
  simp only [normOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

noncomputable abbrev A30p : Subgroup (Perm (Fin Ly0.deg)) :=
  Subgroup.closure ({Ly0.xG, Ly0.y0G, Ly0.w0G} : Set (Perm (Fin Ly0.deg)))

theorem txG_mem_B0 {k : ℕ} (hk : k < 4) : txG k ∈ Ly0.B0 :=
  Ly0.wG_mem Ly0.B0 Ly0.gens0 2 Ly0.gens0_mem _ (txWords_getD_range hk)

theorem txyBp_mem_B0 (hY : Ly1080.YOK) {j : ℕ} (hj : j < 5) : txyBp j ∈ Ly0.B0 := by
  have : txyBp j ∈ Ly0.UYperm := by
    unfold txyBp
    rw [UYperm_eq]
    exact wordG_mem_closure Ly0.uG 4 fun l' hl' => Ly1080.words_range₄ hY _
      (List.mem_append_right _ (Ly1080.txyWords_get_mem hY hj)) l' hl'
  exact Ly0.UYperm_le_B0 this

noncomputable def a3g : ℕ → Perm (Fin Ly0.deg)
  | 0 => Ly0.xG
  | 1 => Ly0.y0G
  | _ => Ly0.w0G

theorem a3Enum_mem (hM : Ly0.ModelChecks)
    (h : mulTreeOK Ly0.deg #[Ly0.tabX, Ly0.tabYw, Ly0.tabW] a3Enum.1 a3Enum.2.1 a3Enum.2.2 = true) :
    ∀ k < a3Enum.1.size, Rep Ly0.deg a3Enum.1[k]! (tablePerm Ly0.deg a3Enum.1[k]!) ∧
      tablePerm Ly0.deg a3Enum.1[k]! ∈ A30p := by
  classical
  have hg : ∀ l < (#[Ly0.tabX, Ly0.tabYw, Ly0.tabW] : Array Table).size,
      Rep Ly0.deg (#[Ly0.tabX, Ly0.tabYw, Ly0.tabW] : Array Table)[l]! (a3g l) ∧ a3g l ∈ A30p := by
    intro l hl
    have hl3 : l < 3 := by simpa using hl
    match l, hl3 with
    | 0, _ =>
      have e : (#[Ly0.tabX, Ly0.tabYw, Ly0.tabW] : Array Table)[0]! = Ly0.tabX := by simp
      rw [e]
      exact ⟨Ly0.rep_X hM.tab hM.struct,
        (Subgroup.subset_closure (Set.mem_insert _ _) : Ly0.xG ∈ A30p)⟩
    | 1, _ =>
      have e : (#[Ly0.tabX, Ly0.tabYw, Ly0.tabW] : Array Table)[1]! = Ly0.tabYw := by simp
      rw [e]
      exact ⟨Ly0.rep_tabYw hM.tab,
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) :
          Ly0.y0G ∈ A30p)⟩
    | 2, _ =>
      have e : (#[Ly0.tabX, Ly0.tabYw, Ly0.tabW] : Array Table)[2]! = Ly0.tabW := by simp
      rw [e]
      exact ⟨Ly0.rep_tabW hM.tab,
        (Subgroup.subset_closure (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_singleton _))) : Ly0.w0G ∈ A30p)⟩
  have hspec := mulTreeOK_spec Ly0.deg_lt A30p hg h
  intro k hk
  obtain ⟨c, hc, hrep⟩ := hspec k hk
  have := tablePerm_eq hrep
  rw [this]
  exact ⟨hrep, hc⟩

theorem memA3_spec (hM : Ly0.ModelChecks)
    (ha : mulTreeOK Ly0.deg #[Ly0.tabX, Ly0.tabYw, Ly0.tabW] a3Enum.1 a3Enum.2.1 a3Enum.2.2 = true)
    {z : Table} {zp : Perm (Fin Ly0.deg)} (hz : Rep Ly0.deg z zp)
    (h : memT Ly0.deg a3Enum.1 z = true) : zp ∈ A30p := by
  obtain ⟨k, hk, hzk⟩ := memT_spec (fun k hk => (a3Enum_mem hM ha k hk).1) hz h
  rw [hzk]
  exact (a3Enum_mem hM ha k hk).2

theorem A30p_mem {a : Perm (Fin Ly0.deg)} (ha : a ∈ A30p) :
    ∃ h : a ∈ Ly0.B0, (⟨a, h⟩ : Ly0.B0) ∈ Ly0.A30 := by
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact ⟨Ly0.xG_mem_B0,
        (Subgroup.subset_closure (Set.mem_insert _ _) : Ly0.xB ∈ Ly0.A30)⟩
    · exact ⟨Ly0.y0G_mem_B0,
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) :
          Ly0.yB ∈ Ly0.A30)⟩
    · exact ⟨Ly0.w0G_mem_B0,
        (Subgroup.subset_closure (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_singleton _))) : Ly0.wB ∈ Ly0.A30)⟩
  | one => exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨hxB, hxA⟩ := ihx
    obtain ⟨hyB, hyA⟩ := ihy
    exact ⟨Subgroup.mul_mem _ hxB hyB, Subgroup.mul_mem _ hxA hyA⟩
  | inv x hx ihx =>
    obtain ⟨hxB, hxA⟩ := ihx
    exact ⟨Subgroup.inv_mem _ hxB, Subgroup.inv_mem _ hxA⟩

theorem txG_mem_Tx (hM : Ly0.ModelChecks) (hn : normOK = true) {k : ℕ} (hk : k < 4) :
    (⟨txG k, txG_mem_B0 hk⟩ : Ly0.B0) ∈ Ly0.Tx := by
  obtain ⟨ha, -, hx⟩ := normOK_parts hn
  have hrep := rep_txB hM.tab hk
  have hrepi := rep_txInvB hM.tab hk
  have hk' := hx k hk
  simp only [normA3OK, Bool.and_eq_true] at hk'
  obtain ⟨⟨h1, h2⟩, h3⟩ := hk'
  have c1 := memA3_spec hM ha (rep_conjT hrep hrepi (Ly0.rep_X hM.tab hM.struct)) h1
  have c2 := memA3_spec hM ha (rep_conjT hrep hrepi (Ly0.rep_tabYw hM.tab)) h2
  have c3 := memA3_spec hM ha (rep_conjT hrep hrepi (Ly0.rep_tabW hM.tab)) h3
  show (⟨txG k, txG_mem_B0 hk⟩ : Ly0.B0) ∈
    normalizer (Subgroup.closure ({Ly0.xB, Ly0.yB, Ly0.wB} : Set Ly0.B0) : Set Ly0.B0)
  refine McLAS.mem_normalizer_closure fun e he => ?_
  rcases he with rfl | rfl | rfl
  · obtain ⟨hB, hmem⟩ := A30p_mem c1
    exact hmem
  · obtain ⟨hB, hmem⟩ := A30p_mem c2
    exact hmem
  · obtain ⟨hB, hmem⟩ := A30p_mem c3
    exact hmem

theorem Pxp_sub_le_Tx (hM : Ly0.ModelChecks) (hn : normOK = true) :
    (Subgroup.closure (txG '' {k | k < 4})).subgroupOf Ly0.B0 ≤ Ly0.Tx := by
  have key : ∀ a ∈ Subgroup.closure (txG '' {k | k < 4}),
      ∃ ha : a ∈ Ly0.B0, (⟨a, ha⟩ : Ly0.B0) ∈ Ly0.Tx := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact ⟨txG_mem_B0 hk, txG_mem_Tx hM hn hk⟩
    | one => exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨hxB, hxT⟩ := ihx
      obtain ⟨hyB, hyT⟩ := ihy
      exact ⟨Subgroup.mul_mem _ hxB hyB, Subgroup.mul_mem _ hxT hyT⟩
    | inv x hx ihx =>
      obtain ⟨hxB, hxT⟩ := ihx
      exact ⟨Subgroup.inv_mem _ hxB, Subgroup.inv_mem _ hxT⟩
  intro b hb
  obtain ⟨hB, hT⟩ := key (b : Perm (Fin Ly0.deg)) hb
  exact hT

theorem normLines_spec (hM : Ly0.ModelChecks) {g gi : Table} {gp : Perm (Fin Ly0.deg)}
    (hg : Rep Ly0.deg g gp) (hgi : Rep Ly0.deg gi gp⁻¹) (h : normLinesOK g gi = true) :
    (gp * Ly0.xG * gp⁻¹ = Ly0.xG ∨ gp * Ly0.xG * gp⁻¹ = Ly0.xG⁻¹) ∧
    (gp * Ly0.y0G * gp⁻¹ = Ly0.y0G ∨ gp * Ly0.y0G * gp⁻¹ = Ly0.y0G⁻¹) ∧
    (gp * Ly0.w0G * gp⁻¹ = Ly0.w0G ∨ gp * Ly0.w0G * gp⁻¹ = Ly0.w0G⁻¹) := by
  simp only [normLinesOK, lineOK, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have rX := Ly0.rep_X hM.tab hM.struct
  have rY := Ly0.rep_tabYw hM.tab
  have rW := Ly0.rep_tabW hM.tab
  refine ⟨?_, ?_, ?_⟩
  · rcases h1 with e | e
    · exact Or.inl ((tblEq_iff_eq (rep_conjT hg hgi rX) rX).1 e)
    · exact Or.inr ((tblEq_iff_eq (rep_conjT hg hgi rX)
        (rep_invT_of_rep Ly0.deg_lt rX)).1 e)
  · rcases h2 with e | e
    · exact Or.inl ((tblEq_iff_eq (rep_conjT hg hgi rY) rY).1 e)
    · exact Or.inr ((tblEq_iff_eq (rep_conjT hg hgi rY) (Ly0.rep_tabYinv hM.tab)).1 e)
  · rcases h3 with e | e
    · exact Or.inl ((tblEq_iff_eq (rep_conjT hg hgi rW) rW).1 e)
    · exact Or.inr ((tblEq_iff_eq (rep_conjT hg hgi rW) (Ly0.rep_tabWinv hM.tab)).1 e)

theorem txyBp_mem_Txy (hM : Ly0.ModelChecks) (hY : Ly1080.YOK) (hn : normOK = true)
    {j : ℕ} (hj : j < 5) : (⟨txyBp j, txyBp_mem_B0 hY hj⟩ : Ly0.B0) ∈ Ly0.Txy := by
  obtain ⟨-, hl, -⟩ := normOK_parts hn
  have rg := rep_txyB hM hY hj
  have rgi := rep_invT_of_rep Ly0.deg_lt rg
  obtain ⟨c1, c2, c3⟩ := normLines_spec hM rg rgi (hl j hj)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine mem_normalizer_zpowers_of_conj ?_
    rcases c1 with e | e
    · have : (⟨txyBp j, txyBp_mem_B0 hY hj⟩ : Ly0.B0) * Ly0.xB *
          (⟨txyBp j, txyBp_mem_B0 hY hj⟩ : Ly0.B0)⁻¹ = Ly0.xB := Subtype.ext e
      rw [this]; exact mem_zpowers _
    · have : (⟨txyBp j, txyBp_mem_B0 hY hj⟩ : Ly0.B0) * Ly0.xB *
          (⟨txyBp j, txyBp_mem_B0 hY hj⟩ : Ly0.B0)⁻¹ = Ly0.xB⁻¹ := Subtype.ext e
      rw [this]; exact inv_mem (mem_zpowers _)
  · refine mem_normalizer_zpowers_of_conj ?_
    rcases c2 with e | e
    · have : (⟨txyBp j, txyBp_mem_B0 hY hj⟩ : Ly0.B0) * Ly0.yB *
          (⟨txyBp j, txyBp_mem_B0 hY hj⟩ : Ly0.B0)⁻¹ = Ly0.yB := Subtype.ext e
      rw [this]; exact mem_zpowers _
    · have : (⟨txyBp j, txyBp_mem_B0 hY hj⟩ : Ly0.B0) * Ly0.yB *
          (⟨txyBp j, txyBp_mem_B0 hY hj⟩ : Ly0.B0)⁻¹ = Ly0.yB⁻¹ := Subtype.ext e
      rw [this]; exact inv_mem (mem_zpowers _)
  · refine mem_normalizer_zpowers_of_conj ?_
    rcases c3 with e | e
    · have : (⟨txyBp j, txyBp_mem_B0 hY hj⟩ : Ly0.B0) * Ly0.wB *
          (⟨txyBp j, txyBp_mem_B0 hY hj⟩ : Ly0.B0)⁻¹ = Ly0.wB := Subtype.ext e
      rw [this]; exact mem_zpowers _
    · have : (⟨txyBp j, txyBp_mem_B0 hY hj⟩ : Ly0.B0) * Ly0.wB *
          (⟨txyBp j, txyBp_mem_B0 hY hj⟩ : Ly0.B0)⁻¹ = Ly0.wB⁻¹ := Subtype.ext e
      rw [this]; exact inv_mem (mem_zpowers _)

theorem Hb_sub_le_Txy (hM : Ly0.ModelChecks) (hY : Ly1080.YOK) (hn : normOK = true) :
    (Subgroup.closure (txyBp '' {l | l < 5})).subgroupOf Ly0.B0 ≤ Ly0.Txy := by
  have key : ∀ a ∈ Subgroup.closure (txyBp '' {l | l < 5}),
      ∃ ha : a ∈ Ly0.B0, (⟨a, ha⟩ : Ly0.B0) ∈ Ly0.Txy := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact ⟨txyBp_mem_B0 hY hl, txyBp_mem_Txy hM hY hn hl⟩
    | one => exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨hxB, hxT⟩ := ihx
      obtain ⟨hyB, hyT⟩ := ihy
      exact ⟨Subgroup.mul_mem _ hxB hyB, Subgroup.mul_mem _ hxT hyT⟩
    | inv x hx ihx =>
      obtain ⟨hxB, hxT⟩ := ihx
      exact ⟨Subgroup.inv_mem _ hxB, Subgroup.inv_mem _ hxT⟩
  intro b hb
  obtain ⟨hB, hT⟩ := key (b : Perm (Fin Ly0.deg)) hb
  exact hT

theorem Pxp_le_B0 : Subgroup.closure (txG '' {k | k < 4}) ≤ Ly0.B0 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  exact txG_mem_B0 hk

theorem Hb_le_B0 (hY : Ly1080.YOK) :
    Subgroup.closure (txyBp '' {l | l < 5}) ≤ Ly0.B0 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨l, hl, rfl⟩
  exact txyBp_mem_B0 hY hl

theorem txyBp_mem_UYperm (hY : Ly1080.YOK) {j : ℕ} (hj : j < 5) :
    txyBp j ∈ Ly0.UYperm := by
  unfold txyBp
  rw [UYperm_eq]
  exact wordG_mem_closure Ly0.uG 4 fun l' hl' => Ly1080.words_range₄ hY _
    (List.mem_append_right _ (Ly1080.txyWords_get_mem hY hj)) l' hl'

theorem nonempty_modelGlue (hM : Ly0.ModelChecks) (hY : Ly1080.YOK)
    (hT : Ly243.trCheck = true) (hτ : Tau.tauOK = true) (hg : glueCheck = true)
    (hcY : Nat.card Ly0.Y0 ≤ 349920) (hcT : Nat.card Ly0.Tx ≤ 7776)
    (hcK : Nat.card Ly0.Txy ≤ 3888) : Nonempty ModelGlue := by
  classical
  obtain ⟨htree, hy, hx, hn⟩ := glueCheck_parts hg
  obtain ⟨Φy, hΦy1, hΦy2, hΦy3, hΦy4⟩ := exists_yEquiv hM hY hτ htree hy
  obtain ⟨Φx, hΦx1, hΦx2, hΦx3, hΦx4⟩ := exists_xEquiv hM hY hT hτ htree hx
  have eY : Ly0.UYperm.subgroupOf Ly0.B0 = Ly0.Y0 := by
    have hle : Ly0.UYperm.subgroupOf Ly0.B0 ≤ Ly0.Y0 :=
      Ly0.UY_le_Y0 hM.tab hM.struct hM.cp1 hM.inv
    have hc : Nat.card (Ly0.UYperm.subgroupOf Ly0.B0) = 349920 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ly0.UYperm_le_B0).toEquiv]
      exact hΦy4
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc]; exact hcY)
  have eT : (Subgroup.closure (txG '' {k | k < 4})).subgroupOf Ly0.B0 = Ly0.Tx := by
    have hc : Nat.card ((Subgroup.closure (txG '' {k | k < 4})).subgroupOf Ly0.B0) = 7776 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Pxp_le_B0).toEquiv]
      exact hΦx4
    exact Subgroup.eq_of_le_of_card_ge (Pxp_sub_le_Tx hM hn) (by rw [hc]; exact hcT)
  have eK : (Subgroup.closure (txyBp '' {l | l < 5})).subgroupOf Ly0.B0 = Ly0.Txy := by
    have hHb : Nat.card ↥(Subgroup.closure (txyBp '' {l | l < 5})) = 3888 := by
      obtain ⟨-, ι, -, -⟩ := exists_treeIso1080 hM hY hτ htree
      rw [Nat.card_congr ι.toEquiv]
      exact Ly1080.card_Txy0 hY
    have hc : Nat.card ((Subgroup.closure (txyBp '' {l | l < 5})).subgroupOf Ly0.B0) = 3888 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Hb_le_B0 hY)).toEquiv]
      exact hHb
    exact Subgroup.eq_of_le_of_card_ge (Hb_sub_le_Txy hM hY hn) (by rw [hc]; exact hcK)
  have hmemUY : ∀ b0 : Ly0.B0, b0 ∈ Ly0.Y0 → (b0 : Perm (Fin Ly0.deg)) ∈ Ly0.UYperm := by
    intro b0 hb
    rw [← eY] at hb
    exact hb
  have hmemUT : ∀ b0 : Ly0.B0, b0 ∈ Ly0.Tx →
      (b0 : Perm (Fin Ly0.deg)) ∈ Subgroup.closure (txG '' {k | k < 4}) := by
    intro b0 hb
    rw [← eT] at hb
    exact hb
  let ιY : ↥Ly0.Y0 ≃* ↥Ly1080.Y0 := (MulEquiv.subgroupCongr eY).symm.trans
    ((Subgroup.subgroupOfEquivOfLe Ly0.UYperm_le_B0).trans Φy)
  let ιT : ↥Ly0.Tx ≃* ↥Ly243.Tx0 := (MulEquiv.subgroupCongr eT).symm.trans
    ((Subgroup.subgroupOfEquivOfLe Pxp_le_B0).trans Φx)
  have hιY : ∀ (b0 : Ly0.B0) (hb : b0 ∈ Ly0.Y0) (hUY : (b0 : Perm (Fin Ly0.deg)) ∈ Ly0.UYperm),
      (ιY ⟨b0, hb⟩ : Perm (Fin Ly1080.deg)) = (Φy ⟨(b0 : Perm (Fin Ly0.deg)), hUY⟩ :
        Perm (Fin Ly1080.deg)) := fun _ _ _ => rfl
  have hιT : ∀ (b0 : Ly0.B0) (hb : b0 ∈ Ly0.Tx)
      (hUT : (b0 : Perm (Fin Ly0.deg)) ∈ Subgroup.closure (txG '' {k | k < 4})),
      (ιT ⟨b0, hb⟩ : Perm (Fin Ly243.deg)) = (Φx ⟨(b0 : Perm (Fin Ly0.deg)), hUT⟩ :
        Perm (Fin Ly243.deg)) := fun _ _ _ => rfl
  refine ⟨{
    ιY := ιY
    ιT := ιT
    tx := fun i => ⟨⟨txG i.val, txG_mem_B0 i.isLt⟩, txG_mem_Tx hM hn i.isLt⟩
    txW := fun i => txWords.getD i.val []
    txW_range := fun i => txWords_getD_range i.isLt
    tx_val := fun i => rfl
    ιY_u := ?_
    ιT_tx := ?_
    K_iff := ?_
    agree := ?_ }⟩
  · intro i hi
    have hu : Ly0.uG i ∈ Ly0.UYperm := Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩
    have h : Ly0.uB i ∈ Ly0.Y0 := by
      rw [← eY]
      exact hu
    refine ⟨h, ?_⟩
    rw [hιY _ h hu]
    exact hΦy1 i hi hu
  · intro i
    have hmem : txG i.val ∈ Subgroup.closure (txG '' {k | k < 4}) :=
      Subgroup.subset_closure ⟨i.val, i.isLt, rfl⟩
    show ((ιT ⟨⟨txG i.val, txG_mem_B0 i.isLt⟩, txG_mem_Tx hM hn i.isLt⟩ : ↥Ly243.Tx0) :
      Perm (Fin Ly243.deg)) = Ly243.gg i.val
    rw [hιT _ _ hmem]
    exact hΦx1 i.val i.isLt hmem
  · intro b
    obtain ⟨b0, hb⟩ := b
    have hUY := hmemUY b0 hb
    have hK : b0 ∈ Ly0.Txy ↔
        (b0 : Perm (Fin Ly0.deg)) ∈ Subgroup.closure (txyBp '' {l | l < 5}) := by
      rw [← eK]
      exact Iff.rfl
    show b0 ∈ Ly0.Txy ↔ ((ιY ⟨b0, hb⟩ : ↥Ly1080.Y0) : Perm (Fin Ly1080.deg)) ∈ Ly1080.Txy0
    rw [hK, hιY b0 hb hUY]
    exact hΦy2 _ hUY
  · intro j b0 hbY hbT hj hyj
    have hUY := hmemUY b0 hbY
    have hUT := hmemUT b0 hbT
    have hmemH : txyBp j ∈ Ly0.UYperm := txyBp_mem_UYperm hY hj
    have h3 := hΦy3 j hj hmemH
    rw [hιY b0 hbY hUY] at hyj
    have h4 : (Φy ⟨(b0 : Perm (Fin Ly0.deg)), hUY⟩ : ↥Ly1080.Y0) = Φy ⟨txyBp j, hmemH⟩ :=
      Subtype.ext (hyj.trans h3.symm)
    have h5 := Φy.injective h4
    have h6 : (b0 : Perm (Fin Ly0.deg)) = txyBp j := congrArg Subtype.val h5
    have hmemX : txyBp j ∈ Subgroup.closure (txG '' {k | k < 4}) := h6 ▸ hUT
    rw [hιT b0 hbT hUT]
    have e : (⟨(b0 : Perm (Fin Ly0.deg)), hUT⟩ : ↥(Subgroup.closure (txG '' {k | k < 4}))) =
        ⟨txyBp j, hmemX⟩ := Subtype.ext h6
    rw [e]
    exact hΦx3 j hj hmemX

end CFSG.Sporadic.Recognition.LyonsSims.Glue
