module

public import Certificates.Certificate9685
public import Certificates.Certificate9686

public section

namespace CFSG.Quasithin.J4ZCent

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.ZCent
open CFSG.Sporadic.J4.QT (Mx Mx_injective)
open CFSG.Quasithin.J4M2 (gE gmats gmats_size M2 cE Kgrp Qgrp rho sigPerm phiRN Mx_gE gE_mem_M2
  rowsMatrix_inv_of_mul rho_gE_perm)
open CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat (p5Gens)
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat (RN rawIsEnc closedH elts eqCert
  closure_eq_of_eqCert card_closure_of_closedH mem_closure_iff_H)
open scoped commutatorElement

theorem r0Facts_spec : R0Facts :=
  Certificates.certificate9685

theorem b0Facts_spec : B0Facts :=
  Certificates.certificate9686

@[expose] def SD : Setup := setup gmats

@[expose] def gmI : Array (Array V2) := gmats.map invRows

theorem chkBase_parts {gm : Array (Array V2)} {S : Setup} (h : chkBase gm S = true) :
    gm.size = 32 ∧
      (∀ n < 32, wfR gm[n]! = true ∧ eqRows (mulT gm[n]! S.git[n]!) idRows = true) ∧
      (∀ i < 16, eqRows (mulT S.b[i]! S.bit[i]!) idRows = true) ∧
      (∀ i < 60, eqRows (mulT S.t[i]! (frTable S.ti[i]!)) idRows = true) := by
  simp only [chkBase, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h5, h6, h7⟩

theorem gmI_getElem {n : ℕ} (hn : n < 32) : gmI[n]! = invRows gmats[n]! := by
  have h : n < gmats.size := by rw [gmats_size]; exact hn
  unfold gmI
  rw [getElem!_pos _ n (by simpa using h), getElem!_pos gmats n h]
  simp

theorem gmI_size : gmI.size = 32 := by
  unfold gmI
  rw [Array.size_map, gmats_size]

theorem SD_git_getElem {n : ℕ} (hn : n < 32) : SD.git[n]! = frTable gmI[n]! :=
  getElem!_map_frTable (m := gmI) (by rw [gmI_size]; exact hn)

theorem g0W_ok : ∀ w ∈ g0W, WordOK 32 w := by
  unfold WordOK
  decide

theorem rW_ok : ∀ w ∈ rW, WordOK 16 w := by
  unfold WordOK
  decide

theorem tW_ok : ∀ w ∈ tW, WordOK 16 w := by
  unfold WordOK
  decide

theorem perfW_ok : ∀ l ∈ perfW, ∀ p ∈ l, WordOK 16 p.1 ∧ WordOK 16 p.2 := by
  unfold WordOK
  decide

theorem getD_ok {k : ℕ} {L : List (List ℤ)} (h : ∀ w ∈ L, WordOK k w) (i : ℕ) :
    WordOK k (L.getD i []) := by
  by_cases hi : i < L.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    intro l hl
    simp at hl

theorem b0El_mem {i : ℕ} (hi : i < 16) : b0El i ∈ B0 :=
  Subgroup.subset_closure (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)

theorem evalW_b0El_mem {w : List ℤ} (hw : WordOK 16 w) : evalW b0El w ∈ B0 :=
  mem_of_evalW b0El (fun _ hn => b0El_mem hn) hw

theorem rEl_mem {j : ℕ} (hj : j < 15) : rEl j ∈ R0 :=
  Subgroup.subset_closure (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)

theorem R0_le_B0 : R0 ≤ B0 := by
  rw [R0, Subgroup.closure_le]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact evalW_b0El_mem (getD_ok rW_ok j)

theorem tEl_mem_B0 (i : ℕ) : tEl i ∈ B0 := evalW_b0El_mem (getD_ok tW_ok i)

theorem b0El_eq_one {i : ℕ} (hi : 16 ≤ i) : b0El i = 1 := by
  unfold b0El
  rw [List.getD_eq_default _ _ (by simp [g0W]; omega)]
  rfl

section Generators

variable (hM : MatFacts) (hb : chkBase gmats SD = true)
include hM hb

theorem Mx_gE_inv {n : ℕ} (hn : n < 32) :
    Mx (gE n) = rowsMatrix gmats[n]! ∧ Mx (gE n)⁻¹ = rowsMatrix gmI[n]! ∧
      wfR gmats[n]! = true ∧ wfR gmI[n]! = true := by
  obtain ⟨-, hbase, -⟩ := chkBase_parts hb
  obtain ⟨hw, hinv⟩ := hbase n hn
  rw [SD_git_getElem hn] at hinv
  refine ⟨Mx_gE hM hn, rowsMatrix_inv_of_mul (Mx_gE hM hn) hinv, hw, ?_⟩
  rw [gmI_getElem hn]
  exact wfR_invRows _

end Generators

theorem SD_b_getElem {i : ℕ} (hi : i < 16) :
    SD.b[i]! = wordT SD.gt SD.git (g0W.getD i []) := by
  have h : i < g0W.length := by simpa [g0W] using hi
  show ((g0W.map (wordT (gtOf gmats) (gitOf gmats))).toArray)[i]! = _
  rw [getElem!_pos _ i (by simpa using h), List.getElem_toArray, List.getElem_map,
    List.getD_eq_getElem _ _ h]
  rfl

theorem SD_b_size : SD.b.size = 16 := by
  show ((g0W.map (wordT (gtOf gmats) (gitOf gmats))).toArray).size = 16
  simp [g0W]

theorem SD_bi_size : SD.bi.size = 16 := by
  show ((bOf gmats).map invRows).size = 16
  rw [Array.size_map]
  exact SD_b_size

theorem SD_bi_getElem {i : ℕ} (hi : i < 16) : SD.bi[i]! = invRows SD.b[i]! := by
  have h : i < SD.b.size := by rw [SD_b_size]; exact hi
  have h' : i < (bOf gmats).size := h
  show ((bOf gmats).map invRows)[i]! = _
  rw [getElem!_pos _ i (by simpa using h'), getElem!_pos SD.b i h]
  simp
  rfl

section Generators2

variable (hM : MatFacts) (hb : chkBase gmats SD = true)
include hM hb

theorem Mx_b0El {i : ℕ} (hi : i < 16) :
    Mx (b0El i) = rowsMatrix SD.b[i]! ∧ wfR SD.b[i]! = true ∧
      Mx (b0El i)⁻¹ = rowsMatrix SD.bi[i]! ∧ wfR SD.bi[i]! = true := by
  have hs : gmats.size = 32 := gmats_size
  have hmain := rowsMatrix_wordT (gens := gE) (m := gmats) (mi := gmI)
    (fun n hn => (Mx_gE_inv hM hb (by omega)).1)
    (fun n hn => (Mx_gE_inv hM hb (by omega)).2.1)
    (fun n hn => (Mx_gE_inv hM hb (by omega)).2.2.1)
    (fun n hn => (Mx_gE_inv hM hb (by omega)).2.2.2)
    (by rw [gmI_size, hs]) (w := g0W.getD i [])
    (by rw [hs]; exact getD_ok g0W_ok i)
  have hbi : SD.b[i]! = wordT (gmats.map frTable) (gmI.map frTable) (g0W.getD i []) :=
    SD_b_getElem hi
  rw [← hbi] at hmain
  obtain ⟨hw, hm⟩ := hmain
  have hmb : Mx (b0El i) = rowsMatrix SD.b[i]! := hm.symm
  have hinv : eqRows (mulT SD.b[i]! SD.bit[i]!) idRows = true :=
    (chkBase_parts hb).2.2.1 i hi
  have hbit : SD.bit[i]! = frTable SD.bi[i]! := by
    show (SD.bi.map frTable)[i]! = _
    exact getElem!_map_frTable (by rw [SD_bi_size]; exact hi)
  rw [hbit] at hinv
  refine ⟨hmb, hw, rowsMatrix_inv_of_mul hmb hinv, ?_⟩
  rw [SD_bi_getElem hi]
  exact wfR_invRows _

end Generators2

theorem SD_r_getElem {j : ℕ} (hj : j < 15) :
    SD.r[j]! = wordT SD.bt SD.bit (rW.getD j []) := by
  have h : j < rW.length := by simpa [rW] using hj
  show ((rW.map (wordT (btOf gmats) (bitOf gmats))).toArray)[j]! = _
  rw [getElem!_pos _ j (by simpa using h), List.getElem_toArray, List.getElem_map,
    List.getD_eq_getElem _ _ h]
  rfl

theorem SD_r_size : SD.r.size = 15 := by
  show ((rW.map (wordT (btOf gmats) (bitOf gmats))).toArray).size = 15
  simp [rW]

theorem SD_t_getElem {i : ℕ} (hi : i < 60) :
    SD.t[i]! = wordT SD.bt SD.bit (tW.getD i []) := by
  have h : i < tW.length := by simpa [tW] using hi
  show ((tW.map (wordT (btOf gmats) (bitOf gmats))).toArray)[i]! = _
  rw [getElem!_pos _ i (by simpa using h), List.getElem_toArray, List.getElem_map,
    List.getD_eq_getElem _ _ h]
  rfl

theorem SD_t_size : SD.t.size = 60 := by
  show ((tW.map (wordT (btOf gmats) (bitOf gmats))).toArray).size = 60
  simp [tW]

theorem SD_rt_getElem {j : ℕ} (hj : j < 15) : SD.rt[j]! = frTable SD.r[j]! :=
  getElem!_map_frTable (m := SD.r) (by rw [SD_r_size]; exact hj)

theorem SD_ti_getElem {i : ℕ} (hi : i < 60) : SD.ti[i]! = invRows SD.t[i]! := by
  have h : i < SD.t.size := by rw [SD_t_size]; exact hi
  have h' : i < (tOf gmats).size := h
  show ((tOf gmats).map invRows)[i]! = _
  rw [getElem!_pos _ i (by simpa using h'), getElem!_pos SD.t i h]
  simp
  rfl

theorem SD_ti_size : SD.ti.size = 60 := by
  show ((tOf gmats).map invRows).size = 60
  rw [Array.size_map]
  exact SD_t_size

section Words2

variable (hM : MatFacts) (hb : chkBase gmats SD = true)
include hM hb

theorem rowsMatrix_wordB {w : List ℤ} (hw : WordOK 16 w) :
    wfR (wordT SD.bt SD.bit w) = true ∧ rowsMatrix (wordT SD.bt SD.bit w) = Mx (evalW b0El w) :=
  rowsMatrix_wordT (gens := b0El) (m := SD.b) (mi := SD.bi)
    (fun n hn => (Mx_b0El hM hb (by rw [SD_b_size] at hn; exact hn)).1)
    (fun n hn => (Mx_b0El hM hb (by rw [SD_b_size] at hn; exact hn)).2.2.1)
    (fun n hn => (Mx_b0El hM hb (by rw [SD_b_size] at hn; exact hn)).2.1)
    (fun n hn => (Mx_b0El hM hb (by rw [SD_b_size] at hn; exact hn)).2.2.2)
    (by rw [SD_bi_size, SD_b_size]) (by rw [SD_b_size]; exact hw)

theorem Mx_rEl {j : ℕ} (hj : j < 15) :
    Mx (rEl j) = rowsMatrix SD.r[j]! ∧ wfR SD.r[j]! = true := by
  obtain ⟨hw, hm⟩ := rowsMatrix_wordB hM hb (getD_ok rW_ok j)
  rw [← SD_r_getElem hj] at hw hm
  exact ⟨hm.symm, hw⟩

theorem Mx_tEl {i : ℕ} (hi : i < 60) :
    Mx (tEl i) = rowsMatrix SD.t[i]! ∧ wfR SD.t[i]! = true ∧
      Mx (tEl i)⁻¹ = rowsMatrix SD.ti[i]! ∧ wfR SD.ti[i]! = true := by
  obtain ⟨hw, hm⟩ := rowsMatrix_wordB hM hb (getD_ok tW_ok i)
  rw [← SD_t_getElem hi] at hw hm
  have hmt : Mx (tEl i) = rowsMatrix SD.t[i]! := hm.symm
  have hinv := (chkBase_parts hb).2.2.2 i hi
  refine ⟨hmt, hw, rowsMatrix_inv_of_mul hmt hinv, ?_⟩
  rw [SD_ti_getElem hi]
  exact wfR_invRows _

end Words2

theorem foldl_insert_contains {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (f : ℕ → α) (l : List ℕ) (T : Std.HashSet α) (X : α) :
    (l.foldl (fun (T : Std.HashSet α) (c : ℕ) => T.insert (f c)) T).contains X = true ↔
      T.contains X = true ∨ ∃ c ∈ l, f c = X := by
  induction l generalizing T with
  | nil => simp
  | cons c l ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro ((h | h) | ⟨d, hd, h⟩)
      · exact Or.inr ⟨c, List.mem_cons_self, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨d, List.mem_cons_of_mem _ hd, h⟩
    · rintro (h | ⟨d, hd, h⟩)
      · exact Or.inl (Or.inr h)
      · rcases List.mem_cons.1 hd with rfl | hd
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨d, hd, h⟩

theorem setup_rset (gm : Array (Array V2)) : (setup gm).rset = rsetOf (setup gm).rt := by
  simp only [setup]

theorem SD_rset : SD.rset = rsetOf SD.rt := setup_rset gmats

theorem rset_contains_iff (X : Array V2) :
    SD.rset.contains X = true ↔ ∃ c < 32768, rExp SD.rt c = X := by
  rw [SD_rset, rsetOf, foldl_insert_contains]
  simp

@[expose] noncomputable def rProdN (n c : ℕ) : J :=
  (List.range n).foldl (fun acc j => if c.testBit j then acc * rEl j else acc) 1

@[expose] noncomputable def rProd (c : ℕ) : J := rProdN 15 c

@[expose] def rExpN (rt : Array (Array V2)) (n c : ℕ) : Array V2 :=
  (List.range n).foldl (fun acc j => if c.testBit j then mulT acc rt[j]! else acc) idRows

theorem rProdN_mem (n c : ℕ) (hn : n ≤ 15) : rProdN n c ∈ R0 := by
  induction n with
  | zero => exact Subgroup.one_mem _
  | succ n ih =>
    have h1 := ih (by omega)
    unfold rProdN at h1 ⊢
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs
    · exact Subgroup.mul_mem _ h1 (rEl_mem (by omega))
    · exact h1

theorem rProd_mem (c : ℕ) : rProd c ∈ R0 := rProdN_mem 15 c le_rfl

section RProd

variable (hM : MatFacts) (hb : chkBase gmats SD = true)
include hM hb

theorem Mx_rProdN (n c : ℕ) (hn : n ≤ 15) :
    Mx (rProdN n c) = rowsMatrix (rExpN SD.rt n c) ∧ wfR (rExpN SD.rt n c) = true := by
  induction n with
  | zero =>
    refine ⟨?_, wfR_idRows⟩
    simp [rProdN, rExpN, rowsMatrix_idRows]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨hm, hw⟩ := Mx_rEl hM hb (j := n) (by omega)
    unfold rProdN rExpN at ih1 ⊢
    unfold rExpN at ih2
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hc : c.testBit n = true
    · simp only [hc, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [SD_rt_getElem (by omega), rowsMatrix_mulT, map_mul, ih1, hm]
      · rw [SD_rt_getElem (by omega)]
        exact wfR_mulT ih2 hw
    · simp only [hc]
      exact ⟨ih1, ih2⟩

theorem Mx_rProd (c : ℕ) :
    Mx (rProd c) = rowsMatrix (rExp SD.rt c) ∧ wfR (rExp SD.rt c) = true :=
  Mx_rProdN hM hb 15 c le_rfl

end RProd

theorem inTR_iff {S : Setup} {x : Array V2} :
    inTR S x = true ↔ ∃ i < 60, S.rset.contains (mulT S.ti[i]! (frTable x)) = true := by
  simp [inTR]

theorem chkPerf_parts {S : Setup} (h : chkPerf S = true) :
    ∀ i < 16, eqRows (wordT S.bt S.bit (perfWord (perfW.getD i []))) S.b[i]! = true := by
  simp only [chkPerf, List.all_eq_true, List.mem_range] at h
  exact h

theorem rExp_zero (rt : Array (Array V2)) : rExp rt 0 = idRows := by
  simp [rExp]

theorem SD_bit_getElem {i : ℕ} (hi : i < 16) : SD.bit[i]! = frTable SD.bi[i]! :=
  getElem!_map_frTable (m := SD.bi) (by rw [SD_bi_size]; exact hi)

theorem SD_bt_getElem {i : ℕ} (hi : i < 16) : SD.bt[i]! = frTable SD.b[i]! :=
  getElem!_map_frTable (m := SD.b) (by rw [SD_b_size]; exact hi)

theorem tEl_zero : tEl 0 = 1 := rfl

theorem mem_R0_of_rExp (hM : MatFacts) (hb : chkBase gmats SD = true) {x : J} {c : ℕ}
    (hx : Mx x = rowsMatrix (rExp SD.rt c)) : x ∈ R0 := by
  have hxe : x = rProd c := Mx_injective (hx.trans (Mx_rProd hM hb c).1.symm)
  rw [hxe]
  exact rProd_mem c

section R0

variable (hR : R0Facts)
include hR

theorem card_R0 : Nat.card R0 = 2 ^ 15 := hR.card_R0

end R0

section Normal

variable (hR : R0Facts)
include hR

theorem B0_le_normalizer_R0 : B0 ≤ Subgroup.normalizer (R0 : Set J) := fun _ hb =>
  Subgroup.mem_normalizer_fintype fun r hr => hR.normal _ hb r hr

theorem R0_normal {b : J} (hb' : b ∈ B0) {r : J} (hr : r ∈ R0) : b * r * b⁻¹ ∈ R0 :=
  hR.normal b hb' r hr

theorem B0_subset_TR : ∀ x ∈ B0, ∃ i < 60, ∃ r ∈ R0, x = tEl i * r := hR.cover

theorem card_B0_le : Nat.card B0 ≤ 60 * 2 ^ 15 := by
  have h : ∀ x : B0, ∃ p : Fin 60 × R0, (x : J) = tEl p.1 * (p.2 : J) := by
    intro x
    obtain ⟨i, hi, r, hr, hxr⟩ := B0_subset_TR hR x x.2
    exact ⟨(⟨i, hi⟩, ⟨r, hr⟩), hxr⟩
  choose f hf using h
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    rw [hf x, hf y, hxy]
  calc Nat.card B0 ≤ Nat.card (Fin 60 × R0) := Nat.card_le_card_of_injective f hinj
    _ = 60 * 2 ^ 15 := by
      rw [Nat.card_prod, card_R0 hR]
      simp

theorem center_R0 {x : J} (hx : x ∈ R0) (hc : ∀ r ∈ R0, x * r = r * x) :
    ∀ b ∈ B0, x * b = b * x :=
  hR.center x hx hc

end Normal

theorem WordOK.perfWord {k : ℕ} {l : List (List ℤ × List ℤ)}
    (h : ∀ p ∈ l, WordOK k p.1 ∧ WordOK k p.2) : WordOK k (perfWord l) := by
  induction l with
  | nil => intro x hx; simp [CFSG.Sporadic.J4.ZCent.perfWord] at hx
  | cons p l ih =>
    have h1 : CFSG.Sporadic.J4.ZCent.perfWord (p :: l) =
        CFSG.Sporadic.J4.ZCent.commW p.1 p.2 ++ CFSG.Sporadic.J4.ZCent.perfWord l := by
      simp [CFSG.Sporadic.J4.ZCent.perfWord]
    rw [h1]
    exact (WordOK.commW (h p List.mem_cons_self).1 (h p List.mem_cons_self).2).append
      (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem perfW_getD_ok (i : ℕ) : ∀ p ∈ perfW.getD i [], WordOK 16 p.1 ∧ WordOK 16 p.2 := by
  by_cases hi : i < perfW.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact perfW_ok _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    intro p hp
    simp at hp

section Perfect

variable (hM : MatFacts) (hb : chkBase gmats SD = true) (hP : chkPerf SD = true)
include hM hb hP

theorem B0_perfect : ⁅B0, B0⁆ = B0 := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb'
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb') (Subgroup.inv_mem _ ha))
      (Subgroup.inv_mem _ hb')
  · rw [B0, Subgroup.closure_le]
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    have hi' := List.mem_range.1 hi
    have hw : WordOK 16 (perfWord (perfW.getD i [])) := WordOK.perfWord (perfW_getD_ok i)
    obtain ⟨-, hwm⟩ := rowsMatrix_wordB hM hb hw
    obtain ⟨hgm, -, -, -⟩ := Mx_b0El hM hb hi'
    have heq := eqRows_iff.1 (chkPerf_parts hP i hi')
    have hel : b0El i = evalW b0El (perfWord (perfW.getD i [])) := by
      apply Mx_injective
      rw [← hwm, heq, hgm]
    rw [SetLike.mem_coe, hel]
    exact evalW_perfWord_mem b0El (fun n hn => b0El_mem hn) _ (perfW_getD_ok i)

end Perfect

theorem chkK_parts {gm : Array (Array V2)} {S : Setup} (h : chkK gm S = true) :
    eqRows (mulT (cMatZ gm S) (frTable (cInvZ gm S))) idRows = true ∧
      (∀ k < 12, ∀ i < 16, inTR S (mulT (mulT gm[k]! S.bt[i]!) S.git[k]!) = true) ∧
      ∀ i < 16, inTR S (mulT (mulT (cMatZ gm S) S.bt[i]!) (frTable (cInvZ gm S))) = true := by
  simp only [chkK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

section KNorm

variable (hM : MatFacts) (hb : chkBase gmats SD = true) (hK : chkK gmats SD = true)
include hM hb hK

omit hK in
theorem mem_B0_of_inTR {y : J} {X : Array V2} (hy : Mx y = rowsMatrix X)
    (hin : inTR SD X = true) : y ∈ B0 := by
  obtain ⟨i, hi, hmem⟩ := inTR_iff.1 hin
  obtain ⟨c, -, hce⟩ := (rset_contains_iff _).1 hmem
  obtain ⟨-, -, htiinv, -⟩ := Mx_tEl hM hb hi
  have hz : (tEl i)⁻¹ * y ∈ R0 := by
    refine mem_R0_of_rExp hM hb (c := c) ?_
    rw [hce, map_mul, htiinv, hy, rowsMatrix_mulT]
  have : y = tEl i * ((tEl i)⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem _ (tEl_mem_B0 i) (R0_le_B0 hz)

omit hM hb hK in
theorem conj_mem_B0_of_gens {g : J} (h : ∀ i < 16, g * b0El i * g⁻¹ ∈ B0) {x : J} (hx : x ∈ B0) :
    g * x * g⁻¹ ∈ B0 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
    exact h i (List.mem_range.1 hi)
  | one => simp
  | mul x y _ _ ihx ihy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ih =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ih

theorem conj_mem_B0_gE {k : ℕ} (hk : k < 12) {x : J} (hx : x ∈ B0) : gE k * x * (gE k)⁻¹ ∈ B0 := by
  refine conj_mem_B0_of_gens (fun i hi => ?_) hx
  obtain ⟨hgk, hgki, -, -⟩ := Mx_gE_inv hM hb (show k < 32 by omega)
  obtain ⟨hgm, -, -, -⟩ := Mx_b0El hM hb hi
  refine mem_B0_of_inTR hM hb (X := mulT (mulT gmats[k]! SD.bt[i]!) SD.git[k]!) ?_
    ((chkK_parts hK).2.1 k hk i hi)
  rw [map_mul, map_mul, hgk, hgm, hgki, SD_git_getElem (by omega), SD_bt_getElem hi,
    rowsMatrix_mulT, rowsMatrix_mulT]

theorem Mx_cE_inv :
    Mx cE = rowsMatrix (cMatZ gmats SD) ∧ Mx cE⁻¹ = rowsMatrix (cInvZ gmats SD) := by
  obtain ⟨ha, -, -, -⟩ := Mx_gE_inv hM hb (show 12 < 32 by norm_num)
  obtain ⟨hbm, -, -, -⟩ := Mx_gE_inv hM hb (show 13 < 32 by norm_num)
  obtain ⟨-, hai, -, -⟩ := Mx_gE_inv hM hb (show 12 < 32 by norm_num)
  obtain ⟨-, hbi, -, -⟩ := Mx_gE_inv hM hb (show 13 < 32 by norm_num)
  have hc : Mx cE = rowsMatrix (cMatZ gmats SD) := by
    have h1 : SD.gt[13]! = frTable gmats[13]! :=
      getElem!_map_frTable (m := gmats) (by rw [gmats_size]; norm_num)
    unfold cE
    rw [commutatorElement_def, map_mul, map_mul, map_mul, ha, hbm, hai, hbi]
    unfold cMatZ
    rw [h1, SD_git_getElem (by norm_num), SD_git_getElem (by norm_num), rowsMatrix_mulT,
      rowsMatrix_mulT, rowsMatrix_mulT]
  exact ⟨hc, rowsMatrix_inv_of_mul hc (chkK_parts hK).1⟩

theorem conj_mem_B0_cE {x : J} (hx : x ∈ B0) : cE * x * cE⁻¹ ∈ B0 := by
  refine conj_mem_B0_of_gens (fun i hi => ?_) hx
  obtain ⟨hc, hci⟩ := Mx_cE_inv hM hb hK
  obtain ⟨hgm, -, -, -⟩ := Mx_b0El hM hb hi
  refine mem_B0_of_inTR hM hb
    (X := mulT (mulT (cMatZ gmats SD) SD.bt[i]!) (frTable (cInvZ gmats SD))) ?_
    ((chkK_parts hK).2.2 i hi)
  rw [map_mul, map_mul, hc, hgm, hci, SD_bt_getElem hi, rowsMatrix_mulT, rowsMatrix_mulT]

theorem Kgrp_conj_mem_B0 {k : J} (hk : k ∈ Kgrp) {x : J} (hx : x ∈ B0) : k * x * k⁻¹ ∈ B0 := by
  have hQ : Qgrp ≤ Subgroup.normalizer (B0 : Set J) := by
    rw [Qgrp, Subgroup.closure_le]
    rintro _ ⟨n, hn, rfl⟩
    exact Subgroup.mem_normalizer_fintype fun y hy => conj_mem_B0_gE hM hb hK hn hy
  have hc : Subgroup.zpowers cE ≤ Subgroup.normalizer (B0 : Set J) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_normalizer_fintype fun y hy => conj_mem_B0_cE hM hb hK hy
  have hKn : Kgrp ≤ Subgroup.normalizer (B0 : Set J) := sup_le hQ hc
  exact (Subgroup.mem_normalizer_iff.1 (hKn hk) x).1 hx

end KNorm

theorem evalW_congr {G : Type*} [Group G] {g₁ g₂ : ℕ → G} {k : ℕ} (h : ∀ n < k, g₁ n = g₂ n)
    {w : List ℤ} (hw : WordOK k w) : evalW g₁ w = evalW g₂ w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [evalW_cons, evalW_cons, ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')]
    have hl := hw l List.mem_cons_self
    unfold letterOf
    split_ifs
    · rw [h _ (by omega)]
    · rw [h _ (by omega)]

section Rho

variable
  (hF : J4Facts)

@[expose] noncomputable def rhoJ (x : J) : Equiv.Perm (Fin 77) := by
  classical
  exact if h : x ∈ M2 then rho hF ⟨x, h⟩ else 1

theorem rhoJ_of_mem {x : J} (h : x ∈ M2) : rhoJ hF x = rho hF ⟨x, h⟩ := by
  unfold rhoJ
  simp only [h, ↓reduceDIte]

theorem rhoJ_mul {x y : J} (hx : x ∈ M2) (hy : y ∈ M2) :
    rhoJ hF (x * y) = rhoJ hF x * rhoJ hF y := by
  rw [rhoJ_of_mem hF (Subgroup.mul_mem _ hx hy), rhoJ_of_mem hF hx, rhoJ_of_mem hF hy,
    ← map_mul]
  rfl

theorem rhoJ_inv {x : J} (hx : x ∈ M2) : rhoJ hF x⁻¹ = (rhoJ hF x)⁻¹ := by
  rw [rhoJ_of_mem hF (Subgroup.inv_mem _ hx), rhoJ_of_mem hF hx, ← map_inv]
  rfl

theorem rhoJ_one : rhoJ hF 1 = 1 := by
  rw [rhoJ_of_mem hF (Subgroup.one_mem _)]
  exact map_one _

theorem rhoJ_evalW {gens : ℕ → J} {k : ℕ} (hg : ∀ n < k, gens n ∈ M2) {w : List ℤ}
    (hw : WordOK k w) : evalW gens w ∈ M2 ∧ rhoJ hF (evalW gens w) = evalW (rhoJ hF ∘ gens) w := by
  induction w with
  | nil => exact ⟨Subgroup.one_mem _, by simp [evalW_nil, rhoJ_one]⟩
  | cons l w ih =>
    obtain ⟨ih1, ih2⟩ := ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have hl := hw l List.mem_cons_self
    have hlm : letterOf gens l ∈ M2 := letterOf_mem gens hg hl.1 hl.2
    have hlr : rhoJ hF (letterOf gens l) = letterOf (rhoJ hF ∘ gens) l := by
      unfold letterOf
      by_cases h : 0 < l
      · simp only [h, ↓reduceIte, Function.comp]
      · simp only [h, ↓reduceIte, Function.comp]
        exact rhoJ_inv hF (hg _ (by omega))
    refine ⟨?_, ?_⟩
    · rw [evalW_cons]
      exact Subgroup.mul_mem _ hlm ih1
    · rw [evalW_cons, evalW_cons, rhoJ_mul hF hlm ih1, ih2, hlr]

end Rho

section RhoGens

theorem gE_mem_M2_of_lt
    (hM : MatFacts) {n : ℕ} (hn : n < 32) : gE n ∈ M2 := gE_mem_M2 hM hn

theorem rhoJ_gE
    (hF : J4Facts) {n : ℕ} (hn : n < 32) :
    rhoJ hF (gE n) = sigPerm n := by
  rw [rhoJ_of_mem hF (gE_mem_M2 hF.mat hn)]
  exact rho_gE_perm hF hn

theorem g0W_pos : ∀ w ∈ g0W, ∀ l ∈ w, 0 < l := by decide

theorem b0Perm_eq (i : ℕ) : b0Perm i = evalW sigPerm (g0W.getD i []) := by
  have hpos : ∀ l ∈ g0W.getD i [], 0 < l := by
    by_cases hi : i < g0W.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact g0W_pos _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      intro l hl
      simp at hl
  have hmap : (g0W.getD i []).map (fun l => sigPerm (l.toNat - 1)) =
      (g0W.getD i []).map (letterOf sigPerm) :=
    List.map_congr_left fun l hl => by
      unfold letterOf
      simp only [hpos l hl, ↓reduceIte]
  unfold b0Perm evalW
  exact congrArg List.prod hmap

theorem b0El_mem_M2
    (hM : MatFacts) (i : ℕ) : b0El i ∈ M2 :=
  mem_of_evalW gE (fun _ hn => gE_mem_M2_of_lt hM hn) (getD_ok g0W_ok i)

theorem rhoJ_b0El
    (hF : J4Facts) (i : ℕ) : rhoJ hF (b0El i) = b0Perm i := by
  have h := (rhoJ_evalW hF (gens := gE) (k := 32) (fun _ hn => gE_mem_M2_of_lt hF.mat hn)
    (getD_ok g0W_ok i)).2
  rw [b0Perm_eq]
  unfold b0El
  rw [h]
  exact evalW_congr (fun n hn => rhoJ_gE hF hn) (getD_ok g0W_ok i)

theorem rhoJ_evalW_b0El
    (hF : J4Facts) {w : List ℤ} (hw : WordOK 16 w) :
    evalW b0El w ∈ M2 ∧ rhoJ hF (evalW b0El w) = wordPerm w := by
  have h := rhoJ_evalW hF (gens := b0El) (k := 16) (fun n _ => b0El_mem_M2 hF.mat n) hw
  refine ⟨h.1, ?_⟩
  rw [h.2]
  have hc : evalW (rhoJ hF ∘ b0El) w = evalW b0Perm w := by
    refine evalW_congr (fun n hn => ?_) hw
    exact rhoJ_b0El hF n
  rw [hc]
  rfl

end RhoGens

section RhoGroups

variable (hρ : B0Facts)
include hρ

theorem closure_b0Perms_eq : Subgroup.closure {p | p ∈ b0Perms} = LamP := hρ.closure_b0

theorem card_LamP : Nat.card LamP = 960 := hρ.card_LamP

theorem tPerm_not_mem_P2 {i : ℕ} (hi : i < 60) (hi0 : i ≠ 0) : tPerm i ∉ P2 :=
  hρ.tPerm_not i hi hi0

end RhoGroups

section RhoB0

variable
  (hF : J4Facts)
include hF

omit
  hF in
theorem B0_le_M2 (hM : MatFacts) : B0 ≤ M2 := by
  rw [B0, Subgroup.closure_le]
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact b0El_mem_M2 hM i

omit
  hF in
theorem R0_le_M2 (hM : MatFacts) : R0 ≤ M2 := R0_le_B0.trans (B0_le_M2 hM)

theorem rhoJ_tEl (i : ℕ) : rhoJ hF (tEl i) = tPerm i :=
  (rhoJ_evalW_b0El hF (getD_ok tW_ok i)).2

theorem tEl_mem_M2 (i : ℕ) : tEl i ∈ M2 := (rhoJ_evalW_b0El hF (getD_ok tW_ok i)).1

theorem rhoJ_mem_closure_b0Perms {x : J} (hx : x ∈ B0) :
    rhoJ hF x ∈ Subgroup.closure {p | p ∈ b0Perms} := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
    rw [rhoJ_b0El hF]
    exact Subgroup.subset_closure (List.mem_map.2 ⟨i, hi, rfl⟩)
  | one => rw [rhoJ_one]; exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    rw [rhoJ_mul hF (B0_le_M2 hF.mat hx) (B0_le_M2 hF.mat hy)]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ih =>
    rw [rhoJ_inv hF (B0_le_M2 hF.mat hx)]
    exact Subgroup.inv_mem _ ih

theorem rhoJ_mem_P2 {x : J} (hx : x ∈ R0) : rhoJ hF x ∈ P2 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    have hj' : j < rW.length := by simpa [rW] using List.mem_range.1 hj
    have h := (rhoJ_evalW_b0El hF (getD_ok rW_ok j)).2
    show rhoJ hF (evalW b0El (rW.getD j [])) ∈ P2
    rw [h]
    refine Subgroup.subset_closure (List.mem_map.2 ⟨rW.getD j [], ?_, rfl⟩)
    rw [List.getD_eq_getElem _ _ hj']
    exact List.getElem_mem hj'
  | one => rw [rhoJ_one]; exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    rw [rhoJ_mul hF (R0_le_M2 hF.mat hx) (R0_le_M2 hF.mat hy)]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ih =>
    rw [rhoJ_inv hF (R0_le_M2 hF.mat hx)]
    exact Subgroup.inv_mem _ ih

end RhoB0

section RhoB

variable
  (hF : J4Facts)

@[expose] noncomputable def rhoB (H : Subgroup J) : Subgroup (Equiv.Perm (Fin 77)) :=
  (H.subgroupOf M2).map (rho hF)

theorem mem_rhoB {H : Subgroup J} {p : Equiv.Perm (Fin 77)} :
    p ∈ rhoB hF H ↔ ∃ x ∈ H, ∃ hx : x ∈ M2, rho hF ⟨x, hx⟩ = p := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, hy, y.2, rfl⟩
  · rintro ⟨x, hx, hxM, rfl⟩
    exact ⟨⟨x, hxM⟩, hx, rfl⟩

include hF

theorem rhoB_B0 (hρ : B0Facts) : rhoB hF B0 = LamP := by
  rw [← closure_b0Perms_eq hρ]
  apply le_antisymm
  · intro p hp
    obtain ⟨x, hx, hxM, rfl⟩ := (mem_rhoB hF).1 hp
    rw [← rhoJ_of_mem hF hxM]
    exact rhoJ_mem_closure_b0Perms hF hx
  · rw [Subgroup.closure_le]
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    refine (mem_rhoB hF).2 ⟨b0El i, b0El_mem (List.mem_range.1 hi), b0El_mem_M2 hF.mat i, ?_⟩
    rw [← rhoJ_of_mem hF (b0El_mem_M2 hF.mat i), rhoJ_b0El hF]

theorem mem_R0_of_rhoJ_eq_one (hρ : B0Facts) (hR : R0Facts) {x : J}
    (hx : x ∈ B0) (h1 : rhoJ hF x = 1) : x ∈ R0 := by
  obtain ⟨i, hi, r, hr, rfl⟩ := B0_subset_TR hR x hx
  rw [rhoJ_mul hF (tEl_mem_M2 hF i) (R0_le_M2 hF.mat hr), rhoJ_tEl hF] at h1
  have hP : tPerm i ∈ P2 := by
    have : tPerm i = (rhoJ hF r)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact Subgroup.inv_mem _ (rhoJ_mem_P2 hF hr)
  by_cases hi0 : i = 0
  · subst hi0
    rw [tEl_zero, one_mul]
    exact hr
  · exact absurd hP (tPerm_not_mem_P2 hρ hi hi0)

end RhoB

end CFSG.Quasithin.J4ZCent
