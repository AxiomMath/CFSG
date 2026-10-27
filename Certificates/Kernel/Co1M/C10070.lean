
module

public import CFSG.Certificates.Kernel.Co1FixCount
public import Certificates.Kernel.Co1M.K10070

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.InvFam
  CFSG.KC.Co1B CFSG.Sporadic.Co1.Module CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative

theorem countsOK_of {S Mt a b : Nat} (hMt : Nat.beq (trK 24 S) Mt = true)
    (h : fixCount (unpackR 24 Mt) = a ∧ fixCountQ (unpackR 24 Mt) (unpackR 24 Qt70) = b) :
    countsOK (unpackR 24 S) a b = true := by
  rw [countsOK, tr_sound hMt, CertificateChecks.KernelCo1Cover.qRows_eq, tr_sound qt_chk, h.1, h.2]
  simp

theorem regT_eq {i : Nat} (hi : i < 65) : Nat.beq (trK 24 (w70.reg i)) (w70.regT i) = true :=
  (CFSG.KC.SortTree.allN_iff _ _).1 w70_tr i hi

theorem sum_map_of_all {f : Nat → Nat} {c : Nat} :
    ∀ L : List Nat, (L.all fun o => Nat.beq (f o) c) = true → (L.map f).sum = L.length * c
  | [], _ => by simp
  | o :: L, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.map_cons, List.sum_cons, sum_map_of_all L h.2, Nat.eq_of_beq_eq_true h.1,
      List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem qA : qCountK 24 Qt70 FA70 0 = 30720 := by
  have e1 : FA70 = FA70.take 4 ++ FAt70 := rfl
  have e2 : CFSG.KC.Co1Fix.spanL (FA70.take 4) 0 = OFF70 := rfl
  rw [e1, CFSG.KC.Co1Fix.qCountK_append, e2, sum_map_of_all OFF70 qs_chk]
  rfl

theorem counts_A70 : countsOK rowsSA 65536 30720 = true := by
  rw [w70_sA]
  refine countsOK_of (regT_eq (by norm_num)) (CFSG.KC.Co1Fix.fixK_sound_of ⟨rfl, rfl, rfl,
    fun f hf => ?_, fixA_pivF, fixA_pivY, qA⟩)
  have h := List.all_eq_true.1 fixA_fix f hf
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem counts_B70 : countsOK rowsSB 4096 0 = true := by
  rw [w70_sB]
  exact countsOK_of (regT_eq (by norm_num)) (CFSG.KC.Co1Fix.fixK_sound fix_B)

theorem counts_C70 : countsOK rowsSC 4096 2048 = true := by
  rw [w70_sC]
  exact countsOK_of (regT_eq (by norm_num)) (CFSG.KC.Co1Fix.fixK_sound fix_C)

end CertificateChecks.KernelCo1M

end
