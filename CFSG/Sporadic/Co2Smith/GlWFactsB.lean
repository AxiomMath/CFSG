module

public import CFSG.Sporadic.Co2Smith.GlWFacts

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Valid


theorem validM_glNJBR {i : ℕ} (hi : i < 10) : Native.validM Native.glNJBR[i]! = true := by
  rw [glNJBR_get hi]
  exact validM_glR (glNJB_letters i hi)

theorem validM_glBitsR (m : ℕ) :
    ∀ l : List ℕ, (∀ i ∈ l, i < 10) → Native.validM (Native.glBitsR Native.glNJBR m l) = true
  | [], _ => by rw [Native.glBitsR, List.foldr_nil]; exact validM_idRows
  | i :: l, hl => by
    have ih := validM_glBitsR m l fun j hj => hl j (List.mem_cons_of_mem _ hj)
    rw [Native.glBitsR, List.foldr_cons]
    split_ifs
    · exact validM_mulRows (validM_glNJBR (hl i List.mem_cons_self)) ih
    · exact ih

theorem validM_glJcR (m : ℕ) : Native.validM (Native.glJcR m) = true :=
  validM_glBitsR m (List.range 10) fun _ hi => List.mem_range.1 hi

theorem validM_glX25 : Native.validM Native.glX25 = true :=
  validM_mulRows (validM_mulRows (validM_glR (by decide)) (validM_glR (by decide)))
    (validM_glR (by decide))

end Valid

section Filter


theorem e2K_val {j : ℕ} :
    (hwK * e1K j * hwKi).val.val = rowsMatrix 22 (Native.glWE2R j) := by
  rw [val_val_mul, val_val_mul, hwK_val, e1K, jcElt_val, hwKi_val, Native.glWE2R,
    rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem glWFilter_spec : ∀ R ∈ Native.glMkDcRows,
    Native.commRows R Native.glX25 = true →
    (∀ k < Native.glWbJ.length, Native.commRows R (Native.glJcR Native.glWbJ[k]!) = true) →
    (∀ k < Native.glWbQ.size, Native.commRows R (Native.glR Native.glWbQ[k]!) = true) →
    ∀ j < 4, Native.commRows R (Native.glWE2R j) = true := by
  have h := glW_parts.2.2.2.2.2.1
  rw [Native.glWFilterOK, List.all_eq_true] at h
  intro R hR hx hJ hQ j hj
  have h' := h R hR
  have hJ' : ((List.range Native.glWbJ.length).all fun k =>
      Native.commRows R (Native.glJcR Native.glWbJ[k]!)) = true :=
    List.all_eq_true.2 fun k hk => hJ k (List.mem_range.1 hk)
  have hQ' : ((List.range Native.glWbQ.size).all fun k =>
      Native.commRows R (Native.glR Native.glWbQ[k]!)) = true :=
    List.all_eq_true.2 fun k hk => hQ k (List.mem_range.1 hk)
  rw [hx, hJ', hQ'] at h'
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h'
  exact List.all_eq_true.1 h' j (List.mem_range.2 hj)

theorem filter_spec {c : K} (hc : c ∈ C0c ⊓ Cz) (hx : c * x25K = x25K * c)
    (hJ : ∀ k < Native.glWbJ.length, c * bJK k = bJK k * c)
    (hQ : ∀ k < Native.glWbQ.size, c * bQK k = bQK k * c) {j : ℕ} (hj : j < 4) :
    c * (hwK * e1K j * hwKi) = hwK * e1K j * hwKi * c := by
  obtain ⟨R, hR, hcR⟩ := exists_rows_D hc
  have hvR := validM_of_mem_glMkDcRows hR
  refine comm_of_commRows hcR e2K_val (glWFilter_spec R hR ?_ ?_ ?_ j hj)
  · exact (comm_iff_rows hcR x25K_val hvR validM_glX25).1 hx
  · intro k hk
    exact (comm_iff_rows hcR (jcElt_val _) hvR (validM_glJcR _)).1 (hJ k hk)
  · intro k hk
    exact (comm_iff_rows hcR (bQK_val hk) hvR
      (validM_glR fun l hl => by have := (glWb_spec.2.2.2.2 k hk).1 l hl; omega)).1 (hQ k hk)

end Filter

theorem glW7_size : Native.glW7.size = 7 := by
  rw [Native.glW7, Array.size_push, glMkGens_size]

theorem glW7_get_lt {k : ℕ} (hk : k < 6) : Native.glW7[k]! = Native.glMkGens[k]! := by
  have hk' : k < Native.glMkGens.size := by rw [glMkGens_size]; exact hk
  rw [Native.glW7, getElem!_pos _ k (by rw [Array.size_push]; omega), Array.getElem_push_lt hk',
    getElem!_pos _ k hk']

theorem glW7_get_six : Native.glW7[6]! = Native.glD1h := by
  rw [Native.glW7, getElem!_pos _ 6 (by rw [Array.size_push, glMkGens_size]; omega),
    Array.getElem_push, dite_eq_right_iff.2 (fun h => absurd h (by rw [glMkGens_size]; omega))]

section Letters


@[expose] noncomputable def w7Letters : Letters where
  elt k := if k < 6 then genLetters.elt k else if k = 6 then δ1hK else 1
  rows := Native.glW7
  val_eq k hk := by
    rw [glW7_size] at hk
    split_ifs with h6 h66
    · rw [glW7_get_lt h6]
      exact genLetters.val_eq k (by rw [genLetters_rows_size]; exact h6)
    · subst h66
      rw [glW7_get_six]
      exact δ1hK_val
    · omega

theorem w7Letters_elt_lt {k : ℕ} (hk : k < 6) : w7Letters.elt k = genLetters.elt k :=
  ite_eq_left hk

theorem w7Letters_elt_six : w7Letters.elt 6 = δ1hK := by
  show (if 6 < 6 then genLetters.elt 6 else if 6 = 6 then δ1hK else 1) = δ1hK
  simp

theorem lWord_w7_eq_gen {w : List ℕ} (hw : ∀ k ∈ w, k < 6) :
    lWord w7Letters w = lWord genLetters w := by
  induction w with
  | nil => simp only [lWord]
  | cons k w ih =>
    have h1 : lWord w7Letters (k :: w) = w7Letters.elt k * lWord w7Letters w := rfl
    have h2 : lWord genLetters (k :: w) = genLetters.elt k * lWord genLetters w := rfl
    rw [h1, h2, w7Letters_elt_lt (hw k List.mem_cons_self),
      ih fun j hj => hw j (List.mem_cons_of_mem _ hj)]

theorem w7Letters_rows : w7Letters.rows = Native.glW7 := rfl

theorem lWord_w7_val {w : List ℕ} (hw : ∀ k ∈ w, k < 7) :
    (lWord w7Letters w).val.val = rowsMatrix 22 (Native.wRows Native.glW7 w) := by
  rw [← w7Letters_rows]
  exact lWord_val w7Letters w fun k hk => by rw [w7Letters_rows, glW7_size]; exact hw k hk


theorem reflK16_eq : reflK 16 = lWord w7Letters Native.glWr0 := by
  have h := glW_parts.2.2.2.2.2.2.1
  simp only [Native.glWr0OK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  exact eq_of_rows (reflK_val (by norm_num)) (lWord_w7_val h.1) h.2.symm

theorem lWord_w7_rel {w : List ℕ} (hw : w ∈ Native.glWRelsN) : lWord w7Letters w = 1 := by
  have h := glW_parts.2.2.2.2.2.2.2.2.1
  simp only [Native.glWRelOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  exact eq_of_rows (lWord_w7_val (h w hw).1) val_one_rows (h w hw).2

theorem glWRelsN_lt {w : List ℕ} (hw : w ∈ Native.glWRelsN) : ∀ k ∈ w, k < 7 := by
  have h := glW_parts.2.2.2.2.2.2.2.2.1
  simp only [Native.glWRelOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  exact (h w hw).1

theorem δ0hK_eq : δ0hK = lWord genLetters Native.glWD0 := by
  have h := glW_parts.2.2.2.2.2.2.2.2.2
  simp only [Native.glWD0OK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  exact eq_of_rows δ0hK_val (genLetters_val h.1) h.2.symm

theorem glWInj_spec {i : ℕ} (hi : i < 20) : Native.glWInj[i]! < 36 ∧
    reflK Native.glWInj[i]! * (reflK (i + 16) * z0) =
      reflK (i + 16) * z0 * reflK Native.glWInj[i]! := by
  have h := glW_parts.2.2.2.2.2.2.2.1
  simp only [Native.glWInjOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨hlt, hc⟩ := h.2 i hi
  exact ⟨hlt, comm_of_commRows (reflK_val hlt) (val_mul_rows (reflK_val (by omega)) z0_val') hc⟩

end Letters

end CFSG.Sporadic.Co2Smith
