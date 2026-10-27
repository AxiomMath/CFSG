module

public import Certificates.Kernel.Co2Smith.Cox
public import Certificates.Kernel.Co2Smith.Root
public import Certificates.Kernel.Co2Smith.WK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem wWords_k : (glNJB.size == 10 && (List.range 10).all (fun i => glNJB[i]!.all (· < 22)) &&
    glWh.all (· < 6) &&
    glWitZ0.all (fun e => e.2.all (· < 22)) && glWitZ1.all (fun e => e.2.all (· < 22)) &&
    glWitZ2.all (fun e => e.2.all (· < 22))) = true := by
  decide +kernel

theorem wWords : glNJB.size = 10 ∧ (∀ i < 10, ∀ k ∈ glNJB[i]!, k < 22) ∧ (∀ k ∈ glWh, k < 6) ∧
    (∀ e ∈ glWitZ0, ∀ k ∈ e.2, k < 22) ∧ (∀ e ∈ glWitZ1, ∀ k ∈ e.2, k < 22) ∧
    (∀ e ∈ glWitZ2, ∀ k ∈ e.2, k < 22) := by
  have h := wWords_k
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem nb_get {i : Nat} (hi : i < 10) : glNJBR[i]! = unpackR 22 (nbK i) := by
  obtain ⟨hs, hw, -⟩ := wWords
  unfold glNJBR nbK
  rw [getElem!_pos _ i (by simp [hs, hi]), Array.getElem_map, ← getElem!_pos glNJB i (by omega),
    glR_eq (hw i hi)]

theorem jc_eq (m : Nat) : glJcR m = unpackR 22 (jcK m) := by
  unfold glJcR glBitsR jcK
  have : ∀ l : List Nat, (∀ i ∈ l, i < 10) → l.foldr (fun i acc => if m.testBit i then
      mulRows 22 glNJBR[i]! acc else acc) (idRows 22) = unpackR 22 (l.foldr
      (fun i acc => if m.testBit i then mulV (nbK i) acc else acc) IDP) := by
    intro l hl
    induction l with
    | nil => exact idRows_eq
    | cons a l ih =>
      rw [List.foldr_cons, List.foldr_cons, ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))]
      split_ifs
      · rw [nb_get (hl a List.mem_cons_self), mulRows_unpack]
      · rfl
  exact this _ (fun i hi => List.mem_range.1 hi)

theorem gens_get {k : Nat} (hk : k < 6) : glMkGens[k]! = unpackR 22 (genK k) := by
  unfold glMkGens genK
  rw [getElem!_pos _ k (by simp [hk]), Array.getElem_ofFn]
  by_cases h0 : k = 0
  · subst h0
    simp only [if_pos rfl]
    exact glZ_eq
  · have h0' : (k == 0) = false := by simp [h0]
    simp only [h0, if_false, h0', Bool.false_eq_true]
    exact mkT_get (by omega)

theorem wGens {w : List Nat} (hw : ∀ k ∈ w, k < 6) : wRows glMkGens w = unpackR 22 (wK genK w) :=
  wRows_unpack _ _ w fun k hk => gens_get (hw k hk)

theorem w7_get {k : Nat} (hk : k < 7) : glW7[k]! = unpackR 22 (w7K k) := by
  unfold glW7 w7K
  by_cases h6 : k = 6
  · subst h6
    rw [getElem!_pos _ 6 (by simp [glMkGens])]
    simp only [glMkGens, Array.getElem_push, Array.size_ofFn, lt_irrefl, if_false, if_pos rfl]
    exact el_eqs.2.2.1
  · have h6' : (k == 6) = false := by simp [h6]
    rw [h6', if_neg Bool.false_ne_true, ← gens_get (by omega),
      getElem!_pos _ k (by simp [glMkGens]; omega), getElem!_pos _ k (by simp [glMkGens]; omega),
      Array.getElem_push_lt]

theorem wW7 {w : List Nat} (hw : ∀ k ∈ w, k < 7) : wRows glW7 w = unpackR 22 (wK w7K w) :=
  wRows_unpack _ _ w fun k hk => w7_get (hw k hk)

theorem wh_eq : glWhR = unpackR 22 whK ∧ glWhiR = unpackR 22 whiK := by
  obtain ⟨-, -, hh, -⟩ := wWords
  exact ⟨wGens hh, wGens fun k hk => hh k (List.mem_reverse.1 hk)⟩

theorem whConj_eq (A : Nat) : glWhConj (unpackR 22 A) = unpackR 22 (whConjK A) := by
  rw [glWhConj, wh_eq.1, wh_eq.2, mulRows_unpack, mulRows_unpack]
  rfl

theorem tab_eq (g : Nat) (tab : List Nat) : glWTabOK (unpackR 22 g) tab = tabWK g tab := by
  unfold glWTabOK tabWK
  congr 1
  apply all_congr_mem
  intro i hi
  rw [List.mem_range] at hi
  rw [nb_get hi, jc_eq, mulRows_unpack, mulRows_unpack, beq_unpack]

theorem dc_eq : glMkDcRows = dcK.map (unpackR 22) := by
  obtain ⟨-, -, -, h0, h1, h2⟩ := wWords
  unfold glMkDcRows dcK
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro e₀ he₀
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro e₁ he₁
  rw [List.map_map]
  apply List.map_congr_left
  intro e₂ he₂
  simp only [Function.comp]
  rw [glR_eq (h0 e₀ he₀), glR_eq (h1 e₁ he₁), glR_eq (h2 e₂ he₂), mulRows_unpack, mulRows_unpack]

theorem wJc_ok : glWJcOK = true := by
  rw [← wJc_k]
  unfold glWJcOK wJcK
  rw [← Array.all_toList]
  congr 1
  apply all_congr_mem
  intro i hi
  rw [List.mem_range] at hi
  rw [nb_get hi, mulRows_unpack, idRows_eq, beq_unpack, glZ_eq, commRows_unpack]
  congr 1
  apply all_congr_mem
  intro j hj
  rw [nb_get (List.mem_range.1 hj), commRows_unpack]

theorem wTabs_ok : glWTabsOK = true := by
  obtain ⟨-, h0, h1, -⟩ := el_eqs
  rw [← wTabs_k]
  unfold glWTabsOK wTabsK
  rw [h1, glAl_eq, glGa_eq, h0, tab_eq, tab_eq, tab_eq, tab_eq]

theorem wE1_ok : glWE1OK = true := by
  rw [← wE1_k]
  unfold glWE1OK wE1K
  congr 1
  apply all_congr_mem
  intro j _
  by_cases ha : (glWE1w[j]!.all (· < 6)) = true
  · by_cases hb : (glWE1iw[j]!.all (· < 6)) = true
    · have ha' : ∀ k ∈ glWE1w[j]!, k < 6 := by simpa using ha
      have hb' : ∀ k ∈ glWE1iw[j]!, k < 6 := by simpa using hb
      rw [ha, hb, jc_eq, jc_eq, wGens ha', wGens hb', beq_unpack, beq_unpack,
        el_eqs.2.2.1, mulRows_unpack, mulRows_unpack, beq_unpack]
    · rw [Bool.not_eq_true] at hb
      simp only [hb, Bool.and_false, Bool.false_and]
  · rw [Bool.not_eq_true] at ha
    simp only [ha, Bool.and_false, Bool.false_and]

theorem wD0_ok : glWD0OK = true := by
  rw [← wD0_k]
  have hw : ∀ k ∈ glWD0, k < 6 := by decide
  unfold glWD0OK wD0K
  rw [wGens hw, el_eqs.2.1, beq_unpack]

theorem whOK_ok : glWhOK = true := by
  obtain ⟨-, -, -, -, -, e25, -⟩ := frame_eqs
  rw [← whOK_k]
  unfold glWhOK whOKK
  rw [wh_eq.1, wh_eq.2, el_eqs.2.2.1, e25, commRows_unpack, commRows_unpack, mulRows_unpack,
    idRows_eq, beq_unpack]

theorem wb_ok : glWbOK = true := by
  obtain ⟨-, -, -, -, -, e25, -⟩ := frame_eqs
  have h := wb_k
  unfold wbK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hs, hJ⟩, hs1⟩, hs2⟩, hQ⟩ := h
  unfold glWbOK
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨hs, fun k hk => ?_⟩, hs1⟩, hs2⟩, fun k hk => ?_⟩
  · rw [jc_eq, whConj_eq, tab_eq]
    exact hJ k hk
  · obtain ⟨⟨⟨⟨ha, hz⟩, h25⟩, ht⟩, hh⟩ := hQ k hk
    have ha' : ∀ x ∈ glWbQ[k]!, x < 22 := fun x hx => by
      have := ha x hx
      simp only [decide_eq_true_eq] at this
      omega
    rw [glR_eq ha', glZ_eq, e25, commRows_unpack, commRows_unpack, tab_eq, whConj_eq, tab_eq]
    exact ⟨⟨⟨⟨ha, hz⟩, h25⟩, ht⟩, hh⟩

theorem wbQ_lt : ∀ k < glWbQ.size, ∀ x ∈ glWbQ[k]!, x < 22 := by
  have h := wb_k
  unfold wbK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  intro k hk x hx
  have := h.2 k hk
  have := this.1.1.1.1 x hx
  omega

theorem filter_ok : glWFilterOK = true := by
  obtain ⟨-, -, -, -, -, e25, -⟩ := frame_eqs
  rw [← filter_k]
  unfold glWFilterOK filterK
  rw [dc_eq, List.all_map]
  apply all_congr_mem
  intro R _
  simp only [Function.comp]
  rw [e25, commRows_unpack]
  have h1 : ((List.range glWbJ.length).all fun k => commRows (unpackR 22 R) (glJcR glWbJ[k]!)) =
      (List.range glWbJ.length).all fun k => commK R (jcK glWbJ[k]!) := by
    apply all_congr_mem
    intro k _
    rw [jc_eq, commRows_unpack]
  have h2 : ((List.range glWbQ.size).all fun k => commRows (unpackR 22 R) (glR glWbQ[k]!)) =
      (List.range glWbQ.size).all fun k => commK R (wK LP glWbQ[k]!) := by
    apply all_congr_mem
    intro k hk
    rw [glR_eq (wbQ_lt k (List.mem_range.1 hk)), commRows_unpack]
  have h3 : ((List.range 4).all fun j => commRows (unpackR 22 R) (glWE2R j)) =
      (List.range 4).all fun j => commK R (we2K j) := by
    apply all_congr_mem
    intro j _
    rw [glWE2R, wh_eq.1, wh_eq.2, jc_eq, mulRows_unpack, mulRows_unpack, commRows_unpack]
    rfl
  rw [h1, h2, h3]

theorem wr0_ok : glWr0OK = true := by
  rw [← wr0_k]
  have hw : ∀ k ∈ glWr0, k < 7 := by decide
  unfold glWr0OK wr0K
  rw [wW7 hw, mkR_get (by decide), beq_unpack]

theorem wInj_ok : glWInjOK = true := by
  rw [← wInj_k]
  unfold glWInjOK wInjK
  congr 1
  apply all_congr_mem
  intro i hi
  rw [List.mem_range] at hi
  by_cases h : glWInj[i]! < 36
  · rw [decide_eq_true h, mkR_get h, mkR_get (by omega), glZ_eq, mulRows_unpack, commRows_unpack]
    rfl
  · rw [decide_eq_false h, Bool.false_and, Bool.false_and]

theorem wRel_ok : glWRelOK = true := by
  rw [← wRel_k]
  unfold glWRelOK wRelK
  apply all_congr_mem
  intro w _
  by_cases ha : (w.all (· < 7)) = true
  · rw [ha, wW7 (by simpa using ha), idRows_eq, beq_unpack]
  · rw [Bool.not_eq_true] at ha
    simp only [ha, Bool.false_and]

theorem w_ok : glWOK = true := by
  unfold glWOK
  rw [wJc_ok, wTabs_ok, wE1_ok, whOK_ok, wb_ok, filter_ok, wr0_ok, wInj_ok, wRel_ok, wD0_ok]
  rfl

end CertificateChecks.KernelCo2Smith
