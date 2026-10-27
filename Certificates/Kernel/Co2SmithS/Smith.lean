module

public import Certificates.Kernel.Co2SmithS.Seeds
public import Certificates.Kernel.Co2SmithS.ClassK
public import Certificates.Kernel.Co2SmithS.OrbK
public import Certificates.Kernel.Co2SmithS.ElK
public import Certificates.Kernel.Co2SmithS.DirK
public import CFSG.Certificates.Kernel.Co2SmithS.ClassSound
public import CFSG.Certificates.Kernel.Co2SmithS.OrbSound
public import CFSG.Certificates.Kernel.Co2Smith.RowsSound
public import Certificates.Kernel.Co2Smith.Pts
public import Certificates.Kernel.Co2Smith.Cox
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2SmithS

open CFSG.KC.Co2SmithS CFSG.KC.Co2InvS CFSG.KC.Co1F2 CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem colAct_eq (A v : Nat) : colAct (unpackR 22 A) v = mvS A v :=
  KernelCo2Smith.colAct_unpack A v

theorem beta_ok : betaOK seedRowsArr = true := by rw [seeds_eq]; exact beta_k

theorem frame_ok : frameOK seedRowsArr = true := by rw [seeds_eq]; exact frame_k

theorem zeta_ok : zetaOK seedRowsArr = true := by rw [seeds_eq]; exact zeta_k

theorem res_ok : resOK seedRowsArr = true := by rw [seeds_eq]; exact res_k

theorem class_ok' : classOK seedRowsArr = true := by
  rw [seeds_eq]
  exact classOK_of class_ok

theorem hWords_facts : hWords.size = 8 ∧ ∀ i < 8, ∀ k ∈ hWords[i]!, k < 4 := by
  have h := elems_ok
  unfold elemsK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.2, h.1.1.2⟩

theorem hRows_size : (hRows seedRowsArr).size = 8 := by
  simp [hRows, hWords_facts.1]

theorem hRows_get {i : Nat} (hi : i < 8) : (hRows seedRowsArr)[i]! = unpackR 22 (hS i) := by
  have hw : hWords[i]! = hWords[i]'(by rw [hWords_facts.1]; exact hi) := getElem!_pos hWords i _
  unfold hRows
  rw [getElem!_pos _ i (by simp [hWords_facts.1, hi]), Array.getElem_map, ← hw,
    mRows_eq (hWords_facts.2 i hi), hS]

theorem nfRows_eq (s v : Nat) :
    nfRows seedRowsArr (hRows seedRowsArr) s v = unpackR 22 (nfS s v) := by
  unfold nfRows nfS
  have hm : ∀ l : List Nat, (∀ i ∈ l, i < 8) → (l.foldr (fun i acc => if v.testBit i then
      mulRows 22 (hRows seedRowsArr)[i]! acc else acc) (idRows 22)) = unpackR 22 (l.foldr
      (fun i acc => if v.testBit i then mulV (hS i) acc else acc) IDP) := by
    intro l hl
    induction l with
    | nil => exact idRows_eq
    | cons a l ih =>
      rw [List.foldr_cons, List.foldr_cons, ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))]
      split_ifs
      · rw [hRows_get (hl a List.mem_cons_self), mulRows_unpack]
      · rfl
  simp only
  rw [hm _ (fun i hi => List.mem_range.1 hi)]
  split_ifs
  · rw [seeds_get 0 (by decide), mulRows_unpack]
  · rfl

theorem sorted_of_nodupB (l : List Nat) (hl : l.length = 512) (hn : nodupB l = true) :
    ((l.mergeSort fun x y => decide (x ≤ y)).length == 512 &&
      strictIncr (l.mergeSort fun x y => decide (x ≤ y))) = true := by
  have hnd : l.Nodup := by
    clear hl
    induction l with
    | nil => exact List.nodup_nil
    | cons a l ih =>
      simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at hn
      refine List.nodup_cons.2 ⟨fun hm => ?_, ih hn.2⟩
      have : memB a l = true := by
        clear ih hn
        induction l with
        | nil => simp at hm
        | cons b l ih' =>
          simp only [memB, Bool.or_eq_true]
          rcases List.mem_cons.1 hm with e | e
          · left
            rw [e]
            exact Nat.beq_refl b
          · right
            exact ih' e
      rw [this] at hn
      exact Bool.noConfusion hn.1
  have hp := List.mergeSort_perm l (fun x y => decide (x ≤ y))
  have hs : (l.mergeSort fun x y => decide (x ≤ y)).Pairwise (fun x y => x ≤ y) := by
    have := List.pairwise_mergeSort (le := fun x y => decide (x ≤ y))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
    exact this.imp (fun h => by simpa using h)
  have hnd' := hp.nodup_iff.2 hnd
  have hlt : (l.mergeSort fun x y => decide (x ≤ y)).Pairwise (fun x y => x < y) := by
    refine (hs.and hnd').imp ?_
    rintro a b ⟨h1, h2⟩
    omega
  have hsi : ∀ m : List Nat, m.Pairwise (fun x y => x < y) → strictIncr m = true := by
    intro m hm
    induction m with
    | nil => rfl
    | cons a m ih =>
      cases m with
      | nil => rfl
      | cons b m =>
        simp only [strictIncr, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨List.rel_of_pairwise_cons hm List.mem_cons_self, ih hm.of_cons⟩
  rw [hp.length_eq, hl, hsi _ hlt]
  rfl

open CFSG.KC.Co2Smith in
theorem elements_ok : elementsOK seedRowsArr = true := by
  have h := elems_ok
  unfold elemsK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, -⟩, e8⟩, -⟩, ⟨e10a, e10b⟩⟩, e11⟩ := h
  have hz : seedRowsArr[0]! = unpackR 22 (LT 0) := seeds_get 0 (by decide)
  have ha : mRows seedRowsArr [2] = unpackR 22 aS := mRows_eq (by simp)
  have hb : mRows seedRowsArr [3] = unpackR 22 bS := mRows_eq (by simp)
  unfold elementsOK
  simp only [Bool.and_eq_true]
  rw [hz, ha, hb, subId_ok]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [powRows_unpack, idRows_eq, beq_unpack]; exact e1
  · rw [powRows_unpack, idRows_eq, beq_unpack]; exact e2
  · rw [commRows_unpack]; exact e3
  · rw [commRows_unpack]; exact e4
  · rw [colAct_eq]; exact e5
  · rw [colAct_eq]; exact e6
  · rw [hRows_size]; rfl
  · refine Eq.trans (KernelCo2Smith.all_congr_mem fun i hi => ?_) e8
    have hi' : i < 8 := List.mem_range.1 hi
    rw [hRows_get hi', mulRows_unpack, idRows_eq, beq_unpack, commRows_unpack, mulRows_unpack,
      beq_unpack]
    refine congrArg (fun t => (eqK (mulV (hS i) (hS i)) IDP && commK (hS i) (LT 0) &&
      eqK (mulV (hS i) zmS) zmS) && t) (KernelCo2Smith.all_congr_mem fun j hj => ?_)
    rw [hRows_get (List.mem_range.1 hj)]
    by_cases hc : hypC i j = true
    · rw [if_pos hc, if_pos hc, mulRows_unpack, mulRows_unpack, mulRows_unpack, beq_unpack]
    · rw [if_neg hc, if_neg hc, mulRows_unpack, mulRows_unpack, beq_unpack]
  · simp only [nfRows_eq, colAct_eq]
    have hs := sorted_of_nodupB _ (by simpa using e10a) e10b
    unfold sigS at hs
    simpa only [Bool.and_eq_true] using hs
  · simp only [nfRows_eq, colAct_eq]
    exact e11

open CFSG.KC.Co2Smith in
theorem xFpf_ok' : xFpfOK seedRowsArr = true := by
  have h := xFpf_ok
  unfold xFpfK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hl, hs⟩, h⟩ := h
  have hx : (fRows seedRowsArr)[8]! = unpackR 22 xS := by
    unfold fRows
    rw [getElem!_pos _ 8 (by simp [hs]), Array.getElem_map,
      ← getElem!_pos frameWords 8 (by simp [hs]), mRows_eq hl, xS]
  unfold xFpfOK
  simp only [List.all_eq_true]
  intro s hs' v hv
  rw [hx, nfRows_eq, commRows_unpack]
  exact h s hs' v hv

theorem pairStep_eq : ∀ l < 2, ∀ x, pairStep #[mRows seedRowsArr [2], mRows seedRowsArr [3]] l x =
    pairStepK l x := by
  intro l hl x
  rw [mRows_two, mRows_three]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · change colAct (unpackR 22 (mulV (LT 2) IDP)) (x / 4194304) * 4194304 +
      colAct (unpackR 22 (mulV (LT 2) IDP)) (x % 4194304) = _
    rw [colAct_eq, colAct_eq]
    rfl
  · change colAct (unpackR 22 (mulV (LT 3) IDP)) (x / 4194304) * 4194304 +
      colAct (unpackR 22 (mulV (LT 3) IDP)) (x % 4194304) = _
    rw [colAct_eq, colAct_eq]
    rfl

theorem PT_lt (g i : Nat) : PT g i < 17592186044416 := by
  unfold PT CFSG.KC.Enum.pg
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem pair_ok' : pairOK seedRowsArr = true := by
  have hx := pairX_ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    decide_eq_true_eq] at hx
  obtain ⟨⟨⟨hlast, hnot⟩, hu⟩, hv⟩ := hx
  have ho := orbRec_sound (N := 7560) (cap := 20000) (by norm_num) (by norm_num) pairStep_eq
    (Nat.eq_of_beq_eq_true hlast) pair_ok
  unfold pairOK
  simp only
  rw [ho.1, Array.size_ofFn, ho.2 true, seeds_get 0 (by decide), colAct_eq, colAct_eq]
  simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨⟨⟨?_, hu⟩, hv⟩, ?_⟩
  · rw [Bool.eq_false_iff]
    intro hc
    rw [Array.contains_iff_mem, Array.mem_ofFn] at hc
    obtain ⟨i, hi⟩ := hc
    have := hnot i.val i.isLt
    rw [hi] at this
    have e : mvS (LT 0) pairU * 4194304 + mvS (LT 0) pairV =
        CFSG.KC.M1F2.vmF 22 zT pairU * 4194304 + CFSG.KC.M1F2.vmF 22 zT pairV := rfl
    rw [e, Nat.beq_refl] at this
    exact Bool.noConfusion this
  · rw [Array.all_iff_forall]
    intro i hi _
    simp only [Array.getElem_ofFn]
    exact decide_eq_true (PT_lt 0 i)

theorem chain_ok' : chainOK seedRowsArr = true := by
  have h := chain_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hg, hb⟩, ho⟩, hk⟩ := h
  unfold chainOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hg, hb⟩, ho⟩, ?_⟩
  rw [List.all_eq_true] at hk ⊢
  intro k hk6
  obtain ⟨⟨hrec, hw⟩, hfix⟩ := Bool.and_eq_true _ _ ▸ Bool.and_eq_true _ _ ▸ hk k hk6
  have hw' : ∀ l < ((chainGens ())[k]!).size, ∀ x ∈ ((chainGens ())[k]!)[l]!, x < 4 := by
    intro l hl x hx
    rw [List.all_eq_true] at hw
    have hm : ((chainGens ())[k]!)[l]! ∈ ((chainGens ())[k]!).toList := by
      rw [getElem!_pos _ l hl]
      exact Array.getElem_mem_toList hl
    have := hw _ hm
    exact of_decide_eq_true (List.all_eq_true.1 this x hx)
  have hG : ∀ l < ((chainGens ())[k]!).size,
      (((chainGens ())[k]!).map (mRows seedRowsArr))[l]! =
        unpackR 22 (wK LT (((chainGens ())[k]!)[l]!)) := by
    intro l hl
    rw [getElem!_pos _ l (by simpa using hl), Array.getElem_map, ← getElem!_pos _ l hl,
      mRows_eq (hw' l hl)]
  have hstep : ∀ l < (((chainGens ())[k]!).map (mRows seedRowsArr)).size, ∀ x,
      vecStep (((chainGens ())[k]!).map (mRows seedRowsArr)) l x = chainStepK k l x := by
    intro l hl x
    rw [Array.size_map] at hl
    unfold vecStep
    rw [hG l hl, colAct_eq]
    rfl
  unfold chainRecOK at hrec
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hrec
  obtain ⟨⟨⟨hr, hl⟩, hpos⟩, hle⟩ := hrec
  have hs := orbRec_sound (cap := 100) hpos hle hstep (Nat.eq_of_beq_eq_true hl) (by
    intro i hi
    rw [Array.size_map]
    exact hr i hi)
  rw [Bool.and_eq_true]
  refine ⟨?_, by rw [hs.1]; exact hs.2 false⟩
  rw [List.all_eq_true] at hfix ⊢
  intro j hj
  have hfj := List.all_eq_true.1 (hfix j hj)
  rw [Array.all_iff_forall]
  intro l hl _
  rw [Array.size_map] at hl
  have e := hfj l (List.mem_range.2 hl)
  rw [Array.getElem_map, ← getElem!_pos _ l hl, mRows_eq (hw' l hl), colAct_eq]
  exact e

theorem smith_ok : betaOK seedRowsArr = true ∧ classOK seedRowsArr = true ∧
    elementsOK seedRowsArr = true ∧ pairOK seedRowsArr = true ∧ chainOK seedRowsArr = true ∧
    frameOK seedRowsArr = true ∧ zetaOK seedRowsArr = true ∧ xFpfOK seedRowsArr = true ∧
    resOK seedRowsArr = true :=
  ⟨beta_ok, class_ok', elements_ok, pair_ok', chain_ok', frame_ok, zeta_ok, xFpf_ok', res_ok⟩

end CertificateChecks.KernelCo2SmithS

end
