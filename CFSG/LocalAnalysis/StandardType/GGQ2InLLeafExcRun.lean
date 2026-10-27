module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafExcCheck

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw.Check

open CFSG.F3.Native CFSG.Decide.F3

theorem noInternalAt_of_zmask_eq_zero {m : Fin 6} {l : List ℕ} (h : zmask m l = 0) :
    NoInternalAt m (vecOfList (dim m) l) := by
  apply noInternalAt_of_forall_ne_zero
  intro i hi
  have hbit : (zmask m l).testBit i.val = true :=
    (testBit_zmask (m := m) l i.isLt).mpr hi
  rw [h, Nat.zero_testBit] at hbit
  exact Bool.false_ne_true hbit

theorem noInternalAt_of_spanOK {m : Fin 6} {l φ : List ℕ} (h : spanOK m l (zmask m l) φ = true) :
    NoInternalAt m (vecOfList (dim m) l) := by
  simp only [spanOK, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h
  obtain ⟨hd, hz⟩ := h
  refine noInternalAt_of_dual (dualOf m φ) ?_ ?_
  · rw [dualOf_vecOfList]
    intro h0
    exact hd (Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff _ 3).mp h0))
  · intro i hi
    have hzm : (zmask m l).testBit i.val = true :=
      (testBit_zmask (m := m) l i.isLt).mpr hi
    have hzh : (zmaskH m φ).testBit i.val = true := by
      have h0 : (zmask m l &&& (full m ^^^ zmaskH m φ)).testBit i.val = false := by
        rw [hz]
        exact Nat.zero_testBit i.val
      rw [Nat.testBit_and, hzm, Bool.true_and, Nat.testBit_xor, testBit_full,
        decide_eq_true i.isLt, Bool.true_xor, Bool.not_eq_false'] at h0
      exact h0
    exact (testBit_zmaskH (m := m) φ i.isLt).mp hzh

private theorem zmask_testBit_of_maskOf {m : Fin 6} {l T : List ℕ}
    (hmask : (maskOf T &&& (full m ^^^ zmask m l)) = 0) {i : Root m} (hi : i.val ∈ T) :
    (zmask m l).testBit i.val = true := by
  have hbt : (maskOf T).testBit i.val = true := (testBit_maskOf T i.val).mpr hi
  have h0 : (maskOf T &&& (full m ^^^ zmask m l)).testBit i.val = false := by
    rw [hmask]
    exact Nat.zero_testBit i.val
  rw [Nat.testBit_and, hbt, Bool.true_and, Nat.testBit_xor, testBit_full,
    decide_eq_true i.isLt, Bool.true_xor, Bool.not_eq_false'] at h0
  exact h0

private theorem testBit_adjM_of_adj {m : Fin 6} {i j : Root m}
    (h : root m i (coroot m j) ≠ 0 ∨ root m j (coroot m i) ≠ 0) :
    (adjM m i).testBit j.val = true := by
  have hAB : (zmask m (((tabH m).getD i []).map mod3) &&&
      zmaskH m (((tabF m).getD i []).map mod3)).testBit j.val = false := by
    rcases h with h1 | h2
    · have hB : (zmaskH m (((tabF m).getD i []).map mod3)).testBit j.val = false := by
        cases hb : (zmaskH m (((tabF m).getD i []).map mod3)).testBit j.val with
        | false => rfl
        | true =>
          exfalso
          have hz := (testBit_zmaskH (m := m) _ j.isLt).mp hb
          rw [dualOf_tabF] at hz
          exact absurd hz h1
      rw [Nat.testBit_and, hB, Bool.and_false]
    · have hA : (zmask m (((tabH m).getD i []).map mod3)).testBit j.val = false := by
        cases hb : (zmask m (((tabH m).getD i []).map mod3)).testBit j.val with
        | false => rfl
        | true =>
          exfalso
          have hz := (testBit_zmask (m := m) _ j.isLt).mp hb
          rw [vecOfList_tabH] at hz
          exact absurd hz h2
      rw [Nat.testBit_and, hA, Bool.false_and]
  simp only [adjM, Nat.testBit_xor, testBit_full, decide_eq_true j.isLt, hAB,
    Bool.true_xor, Bool.not_false]

private theorem exists_root_of_not_mem_mask {m : Fin 6} {l T : List ℕ}
    (hprop : (zmask m l &&& (full m ^^^ maskOf T)) ≠ 0) :
    ∃ j : Root m, root m j (vecOfList (dim m) l) = 0 ∧ j.val ∉ T := by
  obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero hprop
  rw [Nat.testBit_and, Bool.and_eq_true] at hj
  obtain ⟨hzj, hfj⟩ := hj
  have hjlt : j < nroots m := by
    by_contra hge
    have hf : (zmask m l).testBit j = false := testBit_zmask_of_le l (by omega)
    rw [hf] at hzj
    exact Bool.false_ne_true hzj
  have hmaskjf : (maskOf T).testBit j = false := by
    rw [Nat.testBit_xor, testBit_full, decide_eq_true hjlt, Bool.true_xor,
      Bool.not_eq_true'] at hfj
    exact hfj
  refine ⟨⟨j, hjlt⟩, (testBit_zmask (m := m) l hjlt).mp hzj, ?_⟩
  intro hmem
  have hbt : (maskOf T).testBit j = true := (testBit_maskOf T j).mpr hmem
  rw [hmaskjf] at hbt
  exact Bool.false_ne_true hbt

theorem noInternalAt_of_discOK {m : Fin 6} (hb : ∀ i j : Root m, (pairing m i j).natAbs ≤ 2)
    {l T : List ℕ} (h : discOK m (zmask m l) T = true) :
    NoInternalAt m (vecOfList (dim m) l) := by
  simp only [discOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hlt, hne⟩, hmask⟩, hprop⟩, hclosed⟩ := h
  obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp hne
  obtain ⟨j, hjroot, hjmT⟩ := exists_root_of_not_mem_mask hprop
  let T' : Finset (Root m) := Finset.univ.filter fun i => i.val ∈ T
  have memT' : ∀ i : Root m, i ∈ T' ↔ i.val ∈ T := by
    intro i
    simp only [T', Finset.mem_filter, Finset.mem_univ, true_and]
  refine noInternalAt_of_closed (v := vecOfList (dim m) l) T' ?_ ?_ (j₀ := j) ?_ ?_ ?_
  · exact ⟨⟨x, hlt x hx⟩, (memT' _).mpr hx⟩
  · intro i hi
    exact (testBit_zmask (m := m) l i.isLt).mp
      (zmask_testBit_of_maskOf hmask ((memT' i).mp hi))
  · exact hjroot
  · intro hmem
    exact hjmT ((memT' j).mp hmem)
  · intro i hi j' hj' hadj
    have hzj' : (zmask m l).testBit j'.val = true :=
      (testBit_zmask (m := m) l j'.isLt).mpr hj'
    have hadjbit : (adjM m i.val).testBit j'.val = true :=
      testBit_adjM_of_adj ((adj_iff_of_natAbs_pairing_le hb (i := i) (j := j')).mp hadj)
    have h0 : ((adjM m i.val &&& zmask m l) &&& (full m ^^^ maskOf T)).testBit j'.val =
        false := by
      rw [hclosed i.val ((memT' i).mp hi)]
      exact Nat.zero_testBit j'.val
    rw [Nat.testBit_and, Nat.testBit_and, hadjbit, hzj', Bool.true_and,
      Bool.true_and] at h0
    have hmaskj : (maskOf T).testBit j'.val = true := by
      rw [Nat.testBit_xor, testBit_full, decide_eq_true j'.isLt, Bool.true_xor,
        Bool.not_eq_false'] at h0
      exact h0
    exact (memT' j').mpr ((testBit_maskOf T j'.val).mp hmaskj)

theorem noInternalAt_of_run {m : Fin 6} (hb : ∀ i j : Root m, (pairing m i j).natAbs ≤ 2)
    {form : Option (List (List ℕ))} {ls : List (List ℕ)} {cs : List Cert}
    (h : run m form ls cs = true) : ∀ l ∈ ls, NoInternalAt m (vecOfList (dim m) l) := by
  induction ls generalizing cs with
  | nil =>
    intro l hl
    exact absurd hl (List.not_mem_nil)
  | cons l ls ih =>
    intro l' hl'
    simp only [run] at h
    split_ifs at h with hcond
    · rcases List.mem_cons.mp hl' with rfl | hl'
      · rcases Bool.or_eq_true_iff.mp hcond with hz | hd
        · exact noInternalAt_of_zmask_eq_zero (beq_iff_eq.mp hz)
        · cases form with
          | none => exact absurd hd Bool.false_ne_true
          | some M => exact noInternalAt_of_spanOK hd
      · exact ih h l' hl'
    · cases cs with
      | nil => exact absurd h Bool.false_ne_true
      | cons c cs' =>
        rw [Bool.and_eq_true] at h
        obtain ⟨hc, hrs⟩ := h
        rcases List.mem_cons.mp hl' with rfl | hl'
        · cases c with
          | span φ => exact noInternalAt_of_spanOK hc
          | disc T => exact noInternalAt_of_discOK hb hc
        · exact ih hrs l' hl'

theorem noInternalAt_of_run_repVecs {m : Fin 6}
    (hb : ∀ i j : Root m, (pairing m i j).natAbs ≤ 2) {form : Option (List (List ℕ))}
    {cs : List Cert} (h : run m form (repVecs (dim m)) cs = true) {v : V m} (hv : v ≠ 0) :
    NoInternalAt m v := by
  obtain ⟨l, hl, hvl | hvl⟩ := exists_mem_repVecs (d := dim m) (v := v) hv
  · rw [← hvl]
    exact noInternalAt_of_run hb h l hl
  · have hrun : NoInternalAt m (2 • v) := by
      rw [← hvl]
      exact noInternalAt_of_run hb h l hl
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod 3) 2 v] at hrun
    exact (noInternalAt_smul_iff (v := v) (a := (↑(2 : ℕ) : ZMod 3)) (by decide)).mp hrun

end CFSG.StandardType.GGQ2Frame.ExcRaw.Check
