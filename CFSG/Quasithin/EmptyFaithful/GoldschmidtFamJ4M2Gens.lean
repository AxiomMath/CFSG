module

public import Certificates.Certificate4200
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocDef
public import CFSG.Sporadic.J4.QT2ASyl

public section

namespace CFSG.Quasithin.J4M2

open scoped commutatorElement

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4Loc

noncomputable abbrev M2 : Subgroup J := Subgroup.centralizer ({z0} : Set J)

@[expose] noncomputable def gE (n : ℕ) : J := el5 (genWord n)

noncomputable def Dgrp : Subgroup J := Subgroup.closure {x | ∃ n < 32, x = gE n}

theorem zJ_eq : zJ = z0 := rfl

theorem el5_append (w w' : List ℤ) : el5 (w ++ w') = el5 w * el5 w' := wordProd_append gen5 w w'

theorem el5_powWord (w : List ℤ) (e : ℕ) : el5 (powWord w e) = el5 w ^ e := by
  induction e with
  | zero => simp [powWord, el5, wordProd]
  | succ e ih => rw [powWord, el5_append, ih, pow_succ']

theorem gen5_eq_xJ {k : ℕ} (hk : k < 3) : gen5 k = xJ k := by
  simp [gen5, hk]

theorem wordProd_gen5_eq_xJ (w : List ℤ) (hw : ∀ ℓ ∈ w, ℓ ∈ letters) :
    wordProd gen5 w = wordProd xJ w := by
  unfold wordProd
  congr 1
  refine List.map_congr_left fun ℓ hℓ => ?_
  have h := hw ℓ hℓ
  simp only [letters, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gen5_eq_xJ]

theorem genWord_u {j : ℕ} (hj : j < 11) : genWord (17 + j) = uWord j := by
  unfold genWord
  split_ifs <;> first | omega | (congr 1; omega)

theorem genWord_k {i : ℕ} (hi : i < 4) : genWord (28 + i) = kWords.getD i [] := by
  unfold genWord
  split_ifs <;> first | omega | (congr 1; omega)

theorem gE_u {j : ℕ} (hj : j < 11) : gE (17 + j) = uJ j := by
  unfold gE
  rw [genWord_u hj]
  exact wordProd_gen5_eq_xJ _ (uWord_letters.1 j hj)

theorem gE_k {i : ℕ} (hi : i < 4) : gE (28 + i) = kJ i := by
  unfold gE
  rw [genWord_k hi]
  exact wordProd_gen5_eq_xJ _ (kWords_letters i hi)

theorem mulT_frTable (X Y : Array V2) : mulT X (frTable Y) = mulRows X Y := rfl

theorem step_eq (l : Int) :
    (if 0 < l then letT[l.toNat - 1]?.getD idT else letInvT[(-l).toNat - 1]?.getD idT) =
      frTable (if 0 < l then (g5Mats ())[l.toNat - 1]?.getD idRows
        else (g5Invs ())[(-l).toNat - 1]?.getD idRows) := by
  split_ifs
  · simp [letT, letM, Array.getElem?_map, Option.getD_map, idT]
  · simp [letInvT, letInv, Array.getElem?_map, Option.getD_map, idT]

theorem foldl_step_eq (w : List Int) (acc : Array V2) :
    w.foldl (fun (acc : Array V2) (l : Int) => mulT acc (if 0 < l then letT[l.toNat - 1]?.getD idT
        else letInvT[(-l).toNat - 1]?.getD idT)) acc =
      w.foldl (fun acc l => mulRows acc (if 0 < l then (g5Mats ())[l.toNat - 1]?.getD idRows
        else (g5Invs ())[(-l).toNat - 1]?.getD idRows)) acc := by
  induction w generalizing acc with
  | nil => simp only [List.foldl_nil]
  | cons l w ih =>
    simp only [List.foldl_cons]
    rw [step_eq, mulT_frTable]
    exact ih _

theorem wordT_eq_wR (w : List Int) : wordT w = wR w := by
  unfold wordT wR wordRows
  exact foldl_step_eq w idRows

theorem gmats_size : gmats.size = 32 := by
  unfold gmats
  rw [List.size_toArray, List.length_map, List.length_range]

theorem genWord_getElem_gmats {n : ℕ} (hn : n < 32) : gmats[n]! = wordT (genWord n) := by
  have h : n < gmats.size := by rw [gmats_size]; exact hn
  rw [getElem!_pos gmats n h]
  simp [gmats]

theorem uTabs_getElem {j : ℕ} (hj : j < 11) : uTabs[j]! = frTable (wordT (uWord j)) := by
  have h : j < uTabs.size := by
    unfold uTabs
    rw [List.size_toArray, List.length_map, List.length_range]
    exact hj
  rw [getElem!_pos uTabs j h]
  simp [uTabs]

@[expose] def etaMn (n c : ℕ) : Array V2 :=
  (List.range n).foldl (fun acc j => if c.testBit j then mulT acc uTabs[j]! else acc) idRows

theorem etaMn_succ (n c : ℕ) :
    etaMn (n + 1) c = if c.testBit n then mulT (etaMn n c) uTabs[n]! else etaMn n c := by
  unfold etaMn
  rw [List.range_succ, List.foldl_append]
  by_cases h : c.testBit n <;> simp [h]

theorem gtabs_getElem {n : ℕ} (hn : n < 32) : gtabs[n]! = frTable gmats[n]! := by
  have h : n < gtabs.size := by
    unfold gtabs
    rw [Array.size_map, gmats_size]
    exact hn
  rw [getElem!_pos gtabs n h]
  have h2 : n < gmats.size := by rw [gmats_size]; exact hn
  simp [gtabs, getElem!_pos gmats n h2]

section WithFacts

variable (hM : MatFacts)
include hM

theorem Mx_gE {n : ℕ} (hn : n < 32) : Mx (gE n) = rowsMatrix gmats[n]! := by
  rw [genWord_getElem_gmats hn, wordT_eq_wR, gE, Mx_el5 hM]

theorem Mx_uJ' {j : ℕ} (hj : j < 11) :
    Mx (uJ j) = rowsMatrix (wordT (uWord j)) := by
  rw [← gE_u hj, Mx_gE hM (by omega), genWord_getElem_gmats (by omega), genWord_u hj]

theorem rowsMatrix_etaMn (n : ℕ) (hn : n ≤ 11) (c : ℕ) :
    rowsMatrix (etaMn n c) = Mx (eta uJ n c) := by
  induction n with
  | zero => simp [etaMn, eta, rowsMatrix_idRows]
  | succ n ih =>
    rw [etaMn_succ, eta_succ, map_mul]
    have ih' := ih (by omega)
    split_ifs with h
    · rw [uTabs_getElem (j := n) (by omega), mulT_frTable, rowsMatrix_mulRows, ih',
        Mx_uJ' hM (j := n) (by omega)]
    · rw [ih', map_one, mul_one]

theorem rowsMatrix_etaM (c : ℕ) :
    rowsMatrix (etaM c) = Mx (eta uJ 11 c) := rowsMatrix_etaMn hM 11 le_rfl c

theorem rowsMatrix_zM : rowsMatrix zM = Mx z0 :=
  rowsMatrix_etaM hM 1131

theorem gE_mem_M2 {n : ℕ}
    (hn : n < 32) : gE n ∈ M2 := by
  have h := Certificates.certificate4200.1
  unfold chkGens at h
  simp only [List.all_eq_true, Bool.and_eq_true, List.mem_range] at h
  have h1 := (h n hn).2
  have h2 := congrArg rowsMatrix (eqRows_iff.1 h1)
  have e1 : mulT gmats[n]! zT = mulRows gmats[n]! zM := mulT_frTable _ _
  have e2 : mulT zM gtabs[n]! = mulRows zM gmats[n]! := by
    rw [gtabs_getElem hn]
    exact mulT_frTable _ _
  rw [e1, e2, rowsMatrix_mulRows, rowsMatrix_mulRows, ← Mx_gE hM hn, rowsMatrix_zM hM] at h2
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Mx_injective
  rw [map_mul, map_mul]
  exact h2

end WithFacts

theorem gE_mem_Dgrp {n : ℕ} (hn : n < 32) : gE n ∈ Dgrp :=
  Subgroup.subset_closure ⟨n, hn, rfl⟩

theorem Dgrp_le_M2 (hM : MatFacts) :
    Dgrp ≤ M2 := by
  rw [Dgrp, Subgroup.closure_le]
  rintro _ ⟨n, hn, rfl⟩
  exact gE_mem_M2 hM hn

theorem P0_le_Dgrp : P0 ≤ Dgrp := by
  rw [P0, Subgroup.closure_le]
  rintro _ (⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩)
  · rw [← gE_u hj]
    exact gE_mem_Dgrp (by omega)
  · rw [← gE_k hi]
    exact gE_mem_Dgrp (by omega)

@[expose] noncomputable def cE : J := ⁅gE 12, gE 13⁆

theorem cE_mem_M2 (hM : MatFacts) :
    cE ∈ M2 := by
  rw [cE, commutatorElement_def]
  have ha := gE_mem_M2 hM (n := 12) (by norm_num)
  have hb := gE_mem_M2 hM (n := 13) (by norm_num)
  exact M2.mul_mem (M2.mul_mem (M2.mul_mem ha hb) (M2.inv_mem ha)) (M2.inv_mem hb)

section CFacts


theorem rowsMatrix_inv_of_mul {g : J} {X Y : Array V2} (hX : Mx g = rowsMatrix X)
    (hXY : eqRows (mulT X (frTable Y)) idRows = true) : Mx g⁻¹ = rowsMatrix Y := by
  have h := congrArg rowsMatrix (eqRows_iff.1 hXY)
  rw [mulT_frTable, rowsMatrix_mulRows, rowsMatrix_idRows, ← hX] at h
  calc Mx g⁻¹ = Mx g⁻¹ * (Mx g * rowsMatrix Y) := by rw [h, mul_one]
    _ = (Mx g⁻¹ * Mx g) * rowsMatrix Y := by rw [mul_assoc]
    _ = rowsMatrix Y := by rw [← map_mul, inv_mul_cancel, map_one, one_mul]

theorem chkC_spec : chkC = true := Certificates.certificate4200.2.2.2

theorem Mx_cE (hM : MatFacts) : Mx cE = rowsMatrix cMat := by
  have h := chkC_spec
  unfold chkC at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hA, hB⟩, -⟩, -⟩, -⟩, -⟩ := h
  have ha := Mx_gE hM (n := 12) (by norm_num)
  have hb := Mx_gE hM (n := 13) (by norm_num)
  have hai := rowsMatrix_inv_of_mul ha hA
  have hbi := rowsMatrix_inv_of_mul hb hB
  rw [cE, commutatorElement_def, map_mul, map_mul, map_mul, ha, hb, hai, hbi, cMat,
    gtabs_getElem (by norm_num : 13 < 32), mulT_frTable, mulT_frTable, mulT_frTable,
    rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem cE_ne_one (hM : MatFacts) : cE ≠ 1 := by
  have h := chkC_spec
  unfold chkC at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, hW⟩, hN⟩, -⟩, -⟩ := h
  intro hc
  have h1 := ne_of_eqRows_false (X := cMat) (Y := idRows) hW wfR_idRows hN
  apply h1
  rw [← Mx_cE hM, hc, map_one, rowsMatrix_idRows]

theorem cE_pow_three (hM : MatFacts) : cE ^ 3 = 1 := by
  have h := chkC_spec
  unfold chkC at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h3⟩, -⟩ := h
  apply Mx_injective
  have h4 := congrArg rowsMatrix (eqRows_iff.1 h3)
  rw [mulT_frTable, mulT_frTable, rowsMatrix_mulRows, rowsMatrix_mulRows,
    rowsMatrix_idRows, ← Mx_cE hM] at h4
  rw [map_pow, map_one, pow_succ, pow_two]
  exact h4

theorem orderOf_cE (hM : MatFacts) : orderOf cE = 3 :=
  orderOf_eq_prime (cE_pow_three hM) (cE_ne_one hM)

end CFacts

end CFSG.Quasithin.J4M2
