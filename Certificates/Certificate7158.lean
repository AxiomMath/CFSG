module

public import Certificates.Kernel.S8E58.Tables
public import CFSG.Certificates.Kernel.S8E58Sound
import Mathlib.Tactic.IntervalCases

public section

namespace Certificates

open CFSG.KC.Enum CFSG.KS CFSG.KC.S8E58K CFSG.KD.S8E58 CFSG.Quasithin.H13 S8E

theorem k0_of7158 (h : k0B = true) : K0 := by
  intro a ha b hb c hc d hd h1 h2 h3
  unfold k0B at h
  have h' := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1
    (List.all_eq_true.1 h a ha) b hb) c hc) d hd
  have hH : halvesB (ext4 a b c d) = true := by
    unfold halvesB
    unfold Halves at h2
    simpa [List.all_eq_true] using h2
  rw [(beq_iff_eq.2 h1 : (S8E.cmp (ext4 a b c d) (ext4 a b c d) == id8) = true), hH,
    (beq_eq_false_iff_ne.2 h3 : (ext4 a b c d == id8) = false)] at h'
  simpa [List.contains_iff_mem] using h'

theorem tab7158 : TabOK CM MT FX where
  comm a ha b hb := by
    have h := PK.allN_iff.1 (PK.allN_iff.1 ch7158_tcm0 a ha) b hb
    simp only [Bool.and_eq_true] at h
    rw [← beq_iff_eq.1 h.1.1]
    unfold CommL
    simp
  prod a ha b hb hc := by
    have h := PK.allN_iff.1 (PK.allN_iff.1 ch7158_tcm0 a ha) b hb
    simp only [Bool.and_eq_true] at h
    have h2 := h.1.2
    rw [hc] at h2
    simpa [Nat.blt_eq] using h2
  fix a ha p hp := by
    have h := PK.allN_iff.1 (PK.allN_iff.1 ch7158_tfx0 a ha) p hp
    rw [← beq_iff_eq.1 h]
    simp
  inj a ha b hb e := by
    have h := PK.allN_iff.1 (PK.allN_iff.1 ch7158_tcm0 a ha) b hb
    simp only [Bool.and_eq_true] at h
    have h3 := h.2
    rw [e] at h3
    simpa using h3

theorem k34all7158 : ∀ i < 43, k34K CM MT FX R W i = true := by
  intro i hi
  interval_cases i
  exacts [ch7158_k34_0, ch7158_k34_1, ch7158_k34_2, ch7158_k34_3, ch7158_k34_4, ch7158_k34_5,
    ch7158_k34_6, ch7158_k34_7, ch7158_k34_8, ch7158_k34_9, ch7158_k34_10, ch7158_k34_11,
    ch7158_k34_12, ch7158_k34_13, ch7158_k34_14, ch7158_k34_15, ch7158_k34_16, ch7158_k34_17,
    ch7158_k34_18, ch7158_k34_19, ch7158_k34_20, ch7158_k34_21, ch7158_k34_22, ch7158_k34_23,
    ch7158_k34_24, ch7158_k34_25, ch7158_k34_26, ch7158_k34_27, ch7158_k34_28, ch7158_k34_29,
    ch7158_k34_30, ch7158_k34_31, ch7158_k34_32, ch7158_k34_33, ch7158_k34_34, ch7158_k34_35,
    ch7158_k34_36, ch7158_k34_37, ch7158_k34_38, ch7158_k34_39, ch7158_k34_40, ch7158_k34_41,
    ch7158_k34_42]

theorem certificate7158 : CFSG.Quasithin.H13.S8E.s8Check = true :=
  by
    unfold s8Check
    rw [decide_eq_true (k0_of7158 ch7158_k00), decide_eq_true (k34_of tab7158 k34all7158)]
    rfl

end Certificates
