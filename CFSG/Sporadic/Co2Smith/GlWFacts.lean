module

public import CFSG.Sporadic.Co2Smith.GlWCheck
public import CFSG.Sporadic.Co2Smith.GlC0MarkB

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Gen


theorem genLetters_rows_size : genLetters.rows.size = 6 := glMkGens_size

theorem genLetters_val {w : List ℕ} (hw : ∀ k ∈ w, k < 6) :
    (lWord genLetters w).val.val = rowsMatrix 22 (Native.wRows Native.glMkGens w) :=
  lWord_val genLetters w fun k hk => genLetters_rows_size ▸ hw k hk


theorem genLetters_mem_D (k : ℕ) : genLetters.elt k ∈ C0c ⊓ Cz := by
  show (if k = 0 then z0 else if k < 6 then tK (k - 1) else 1) ∈ C0c ⊓ Cz
  split_ifs with h0 h6
  · exact mem_inf.2 ⟨x16K_eq ▸ x16K_mem_C0c, z0_mem_Cz⟩
  · exact mem_inf.2 ⟨tK_mem_C0c (by omega), mem_Cz_of_comm (tK_comm_z0 (by omega))⟩
  · exact (C0c ⊓ Cz).one_mem

theorem lWord_gen_mem_D (w : List ℕ) : lWord genLetters w ∈ C0c ⊓ Cz :=
  lWord_mem_closure genLetters _ genLetters_mem_D w

end Gen

theorem glWh_lt : ∀ k ∈ Native.glWh, k < 6 := by decide

theorem glWh_spec :
    Native.commRows Native.glWhR Native.glD1h = true ∧
    Native.commRows Native.glWhR Native.glX25 = true ∧
    mulRows 22 Native.glWhR Native.glWhiR = idRows 22 := by
  have h := glW_parts.2.2.2.1
  simp only [Native.glWhOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

section H


@[expose] noncomputable def hwK : K := lWord genLetters Native.glWh

@[expose] noncomputable def hwKi : K := lWord genLetters Native.glWh.reverse

theorem hwK_val : hwK.val.val = rowsMatrix 22 Native.glWhR := genLetters_val glWh_lt

theorem hwKi_val : hwKi.val.val = rowsMatrix 22 Native.glWhiR :=
  genLetters_val fun k hk => glWh_lt k (List.mem_reverse.1 hk)


theorem hwK_comm_δ1hK : hwK * δ1hK = δ1hK * hwK := comm_of_commRows hwK_val δ1hK_val glWh_spec.1

theorem hwK_comm_x25K : hwK * x25K = x25K * hwK := comm_of_commRows hwK_val x25K_val glWh_spec.2.1

theorem hwK_mul_hwKi : hwK * hwKi = 1 :=
  eq_of_rows (val_mul_rows hwK_val hwKi_val) val_one_rows glWh_spec.2.2

theorem hwKi_eq : hwKi = hwK⁻¹ := eq_inv_of_mul_eq_one_right hwK_mul_hwKi

end H

section E1


@[expose] noncomputable def e1K (j : ℕ) : K := jcElt Native.glWE1c[j]!

@[expose] noncomputable def e1iK (j : ℕ) : K := jcElt Native.glWE1ic[j]!


theorem glWE1_spec : ∀ j < 4, (∀ k ∈ Native.glWE1w[j]!, k < 6) ∧
    (∀ k ∈ Native.glWE1iw[j]!, k < 6) ∧
    Native.glJcR Native.glWE1c[j]! = Native.wRows Native.glMkGens Native.glWE1w[j]! ∧
    Native.glJcR Native.glWE1ic[j]! = Native.wRows Native.glMkGens Native.glWE1iw[j]! ∧
    mulRows 22 Native.glD1h (Native.glJcR Native.glWE1c[j]!) =
      mulRows 22 (Native.glJcR Native.glWE1ic[j]!) Native.glD1h := by
  have h := glW_parts.2.2.1
  simp only [Native.glWE1OK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  intro j hj
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h.2 j hj
  exact ⟨h2, h3, h4, h5, h6⟩

theorem e1K_eq {j : ℕ} (hj : j < 4) : e1K j = lWord genLetters Native.glWE1w[j]! :=
  eq_of_rows (jcElt_val _) (genLetters_val (glWE1_spec j hj).1) (glWE1_spec j hj).2.2.1

theorem e1iK_eq {j : ℕ} (hj : j < 4) : e1iK j = lWord genLetters Native.glWE1iw[j]! :=
  eq_of_rows (jcElt_val _) (genLetters_val (glWE1_spec j hj).2.1) (glWE1_spec j hj).2.2.2.1

theorem δ1hK_conj_e1K {j : ℕ} (hj : j < 4) : δ1hK * e1K j * δ1hK⁻¹ = e1iK j := by
  have e : δ1hK * e1K j = e1iK j * δ1hK :=
    eq_of_rows (val_mul_rows δ1hK_val (jcElt_val _)) (val_mul_rows (jcElt_val _) δ1hK_val)
      (glWE1_spec j hj).2.2.2.2
  rw [e, mul_inv_cancel_right]

end E1

section B


@[expose] noncomputable def bJK (k : ℕ) : K := jcElt Native.glWbJ[k]!

@[expose] noncomputable def bQK (k : ℕ) : K := glE Native.glWbQ[k]!

theorem glWhConj_val {b : K} {R : Array ℕ} (hb : b.val.val = rowsMatrix 22 R) :
    (hwKi * b * hwK).val.val = rowsMatrix 22 (Native.glWhConj R) := by
  rw [val_val_mul, val_val_mul, hwKi_val, hb, hwK_val, Native.glWhConj, rowsMatrix_mulRows,
    rowsMatrix_mulRows]


theorem glWb_spec :
    Native.glWbJ.length = Native.glWbJh.size ∧
    (∀ k < Native.glWbJ.length, Native.glWbJ[k]! < 1024 ∧
      Native.glWTabOK (Native.glWhConj (Native.glJcR Native.glWbJ[k]!)) Native.glWbJh[k]! =
        true) ∧
    Native.glWbQ.size = Native.glWbQt.size ∧ Native.glWbQ.size = Native.glWbQh.size ∧
    ∀ k < Native.glWbQ.size, (∀ l ∈ Native.glWbQ[k]!, l < 9) ∧
      Native.commRows (Native.glR Native.glWbQ[k]!) Native.glZ = true ∧
      Native.commRows (Native.glR Native.glWbQ[k]!) Native.glX25 = true ∧
      Native.glWTabOK (Native.glR Native.glWbQ[k]!) Native.glWbQt[k]! = true ∧
      Native.glWTabOK (Native.glWhConj (Native.glR Native.glWbQ[k]!)) Native.glWbQh[k]! =
        true := by
  have h := glW_parts.2.2.2.2.1
  simp only [Native.glWbOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun k hk => ?_⟩
  obtain ⟨⟨⟨⟨h6, h7⟩, h8⟩, h9⟩, h10⟩ := h5 k hk
  exact ⟨h6, h7, h8, h9, h10⟩

theorem bQK_val {k : ℕ} (hk : k < Native.glWbQ.size) :
    (bQK k).val.val = rowsMatrix 22 (Native.glR Native.glWbQ[k]!) :=
  glE_val fun l hl => by have := (glWb_spec.2.2.2.2 k hk).1 l hl; omega

theorem bQK_mem_Cz {k : ℕ} (hk : k < Native.glWbQ.size) : bQK k ∈ Cz :=
  mem_Cz_of_comm (comm_of_commRows (bQK_val hk) z0_val' (glWb_spec.2.2.2.2 k hk).2.1)

theorem bQK_comm_x25K {k : ℕ} (hk : k < Native.glWbQ.size) : bQK k * x25K = x25K * bQK k :=
  comm_of_commRows (bQK_val hk) x25K_val (glWb_spec.2.2.2.2 k hk).2.2.1

theorem bQK_mem_N {k : ℕ} (hk : k < Native.glWbQ.size) : bQK k ∈ normalizer (Jc : Set K) :=
  mem_normalizer_of_tab (bQK_val hk) (glWb_spec.2.2.2.2 k hk).2.2.2.1

theorem bQK_conj_mem_N {k : ℕ} (hk : k < Native.glWbQ.size) :
    hwKi * bQK k * hwK ∈ normalizer (Jc : Set K) :=
  mem_normalizer_of_tab (glWhConj_val (bQK_val hk)) (glWb_spec.2.2.2.2 k hk).2.2.2.2

theorem bJK_conj_mem_N {k : ℕ} (hk : k < Native.glWbJ.length) :
    hwKi * bJK k * hwK ∈ normalizer (Jc : Set K) :=
  mem_normalizer_of_tab (glWhConj_val (jcElt_val _)) (glWb_spec.2.1 k hk).2

end B

end CFSG.Sporadic.Co2Smith
