module

public import Certificates.Kernel.S8F28.Tables
public import CFSG.Certificates.Kernel.S8F28Sound
import Mathlib.Tactic.IntervalCases

public section

namespace Certificates

open CFSG.KC.Enum CFSG.KS CFSG.KC.S8F28K CFSG.KD.S8F28 CFSG.Quasithin.H13 S8E S8F

theorem fixB_iff7218 (f u : List Nat) : fixB f u = true ↔ FixL f u := by
  unfold fixB FixL
  simp [List.all_eq_true]

theorem k0_of7218 (h : k0B = true) : K0 := by
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

theorem tab7218 : TabOK CM MT FMK where
  comm a ha b hb := by
    have h := PK.allN_iff.1 (PK.allN_iff.1 ch7218_tcm0 a ha) b hb
    simp only [Bool.and_eq_true] at h
    rw [← beq_iff_eq.1 h.1.1]
    unfold CommL
    simp
  prod a ha b hb hc := by
    have h := PK.allN_iff.1 (PK.allN_iff.1 ch7218_tcm0 a ha) b hb
    simp only [Bool.and_eq_true] at h
    have h2 := h.1.2
    rw [hc] at h2
    simpa [Nat.blt_eq] using h2
  fix a ha v hv := by
    have h := PK.allN_iff.1 (PK.allN_iff.1 ch7218_tfix0 a ha) v hv
    rw [← fixB_iff7218, beq_iff_eq.1 h]
  vec v hv := by
    have h := PK.allN_iff.1 ch7218_tvec0 v hv
    unfold vecB at h
    unfold Vec
    simpa [List.all_eq_true, Nat.blt_eq] using h
  inj a ha b hb e := by
    have h := PK.allN_iff.1 (PK.allN_iff.1 ch7218_tcm0 a ha) b hb
    simp only [Bool.and_eq_true] at h
    have h3 := h.2
    rw [e] at h3
    simpa using h3

theorem c3all7218 : ∀ i < 43, c3K CM MT FMK i = true := by
  intro i hi
  interval_cases i
  exacts [ch7218_c3_0, ch7218_c3_1, ch7218_c3_2, ch7218_c3_3, ch7218_c3_4, ch7218_c3_5,
    ch7218_c3_6, ch7218_c3_7, ch7218_c3_8, ch7218_c3_9, ch7218_c3_10, ch7218_c3_11, ch7218_c3_12,
    ch7218_c3_13, ch7218_c3_14, ch7218_c3_15, ch7218_c3_16, ch7218_c3_17, ch7218_c3_18,
    ch7218_c3_19, ch7218_c3_20, ch7218_c3_21, ch7218_c3_22, ch7218_c3_23, ch7218_c3_24,
    ch7218_c3_25, ch7218_c3_26, ch7218_c3_27, ch7218_c3_28, ch7218_c3_29, ch7218_c3_30,
    ch7218_c3_31, ch7218_c3_32, ch7218_c3_33, ch7218_c3_34, ch7218_c3_35, ch7218_c3_36,
    ch7218_c3_37, ch7218_c3_38, ch7218_c3_39, ch7218_c3_40, ch7218_c3_41, ch7218_c3_42]

theorem c4all7218 : ∀ i < 43, c4K CM MT FMK i = true := by
  intro i hi
  interval_cases i
  exacts [ch7218_c4_0, ch7218_c4_1, ch7218_c4_2, ch7218_c4_3, ch7218_c4_4, ch7218_c4_5,
    ch7218_c4_6, ch7218_c4_7, ch7218_c4_8, ch7218_c4_9, ch7218_c4_10, ch7218_c4_11, ch7218_c4_12,
    ch7218_c4_13, ch7218_c4_14, ch7218_c4_15, ch7218_c4_16, ch7218_c4_17, ch7218_c4_18,
    ch7218_c4_19, ch7218_c4_20, ch7218_c4_21, ch7218_c4_22, ch7218_c4_23, ch7218_c4_24,
    ch7218_c4_25, ch7218_c4_26, ch7218_c4_27, ch7218_c4_28, ch7218_c4_29, ch7218_c4_30,
    ch7218_c4_31, ch7218_c4_32, ch7218_c4_33, ch7218_c4_34, ch7218_c4_35, ch7218_c4_36,
    ch7218_c4_37, ch7218_c4_38, ch7218_c4_39, ch7218_c4_40, ch7218_c4_41, ch7218_c4_42]

theorem certificate7218 : CFSG.Quasithin.H13.S8E.K0 ∧ CFSG.Quasithin.H13.S8F.C2w ∧ CFSG.Quasithin.H13.S8F.C3w ∧
    CFSG.Quasithin.H13.S8F.C4w :=
  ⟨k0_of7218 ch7218_k00, c2w_of tab7218 ch7218_c20, c3w_of tab7218 c3all7218,
    c4w_of tab7218 c4all7218⟩

end Certificates
