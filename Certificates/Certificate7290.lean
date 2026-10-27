module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverOddNative
import Certificates.Kernel.J2Cover.Odd7290
import Certificates.Kernel.J2Cover.M22Bind

namespace CertificateChecks.Batch7290

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3
open CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.J2Cover.Models
open CertificateChecks.KernelJ2Cover CertificateChecks.KernelJ2Cover.Odd7290

theorem mulIdx_eq {a d : Nat} (ha : a < 128) (hd : d < 128) : mulIdx a d = mtK a d := by
  have h := fMT_all a ha
  unfold fMT at h
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h
  unfold mtK
  rw [blt_true ha]
  exact Nat.eq_of_beq_eq_true (allN_spec h2 d hd)

theorem cG3 : CnN 315 9 G3 := wordP_canon _

theorem cG3s : CnN 315 9 G3s := canon_pcN cG3 cG3

theorem cG5 : CnN 315 9 G5 := wordP_canon _

theorem cG5s : CnN 315 9 G5s := canon_pcN cG5 cG5

theorem cG5i : CnN 315 9 G5i := canon_pcN cG5s cG5s

theorem conj_eq {A B k x : Nat} (cA : CnN 315 9 A) (cB : CnN 315 9 B) (hk : k < 128)
    (hx : x < 128) :
    eqA 315 (compA 315 (compA 315 (unpack 315 9 A) eltArrs[k]!) (unpack 315 9 B)) eltArrs[x]! =
      Nat.beq (pc (pc A (ELT k)) B) (ELT x) := by
  rw [eltArrs_eq k hk, eltArrs_eq x hx, compA_unpackN cA (eltT_canon k hk),
    compA_unpackN (canon_pcN cA (eltT_canon k hk)) cB,
    eqA_unpackN (canon_pcN (canon_pcN cA (eltT_canon k hk)) cB) (eltT_canon x hx)]
  rfl

theorem oddCheck_eq : oddCheck () = true := by
  have e3 : wordArr oddW3 = unpack 315 9 G3 := wordArr_eq _
  have e5 : wordArr oddW5 = unpack 315 9 G5 := wordArr_eq _
  have e3s : compA 315 (unpack 315 9 G3) (unpack 315 9 G3) = unpack 315 9 G3s :=
    compA_unpackN cG3 cG3
  have e5s : compA 315 (unpack 315 9 G5) (unpack 315 9 G5) = unpack 315 9 G5s :=
    compA_unpackN cG5 cG5
  have e5i : compA 315 (unpack 315 9 G5s) (unpack 315 9 G5s) = unpack 315 9 G5i :=
    compA_unpackN cG5s cG5s
  have cE4 := eltT_canon 4 (by norm_num)
  unfold oddCheck
  simp only [Bool.and_eq_true]
  rw [e3, e5, e3s, e5s, e5i, eltArrs_eq 4 (by norm_num), ← hId]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [compA_unpackN cG3 cG3s, eqA_unpackN (canon_pcN cG3 cG3s) cId]
    exact k3290
  · rw [eqA_unpackN cG3 cId]
    exact k3n7290
  · rw [compA_unpackN cG5 cG5i, eqA_unpackN (canon_pcN cG5 cG5i) cId]
    exact k5290
  · rw [eqA_unpackN cG5 cId]
    exact k5n7290
  · rw [compA_unpackN cG3 cE4, compA_unpackN cE4 cG3,
      eqA_unpackN (canon_pcN cG3 cE4) (canon_pcN cE4 cG3)]
    exact kc37290
  · rw [compA_unpackN cG5 cE4, compA_unpackN cE4 cG5,
      eqA_unpackN (canon_pcN cG5 cE4) (canon_pcN cE4 cG5)]
    exact kc57290
  · refine CFSG.Monster.B.Co2.allLt_iff.2 fun k hk => ?_
    have h := allN_spec kW7290 k hk
    unfold oddK at h
    cases hw : oddWidxB k
    · rfl
    · rw [hw] at h
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨l1, w1⟩, q1⟩, l2⟩, w2⟩, q2⟩, l3⟩, w3⟩, q3⟩, l4⟩, w4⟩, q4⟩ := h
      rw [conj_eq cG3 cG3s hk l1, conj_eq cG3s cG3 hk l2, conj_eq cG5 cG5i hk l3,
        conj_eq cG5i cG5 hk l4]
      simp [l1, w1, q1, l2, w2, q2, l3, w3, q3, l4, w4, q4]
  · refine CFSG.Monster.B.Co2.allLt_iff.2 fun i hi => ?_
    have h := allN_spec kF7290 i hi
    have hb : bitAt fRows i i = (fRK i).testBit i := by
      unfold bitAt
      rw [← fR_eq]
    rw [mulIdx_eq hi hi, hb]
    exact h

end CertificateChecks.Batch7290

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.J2Cover.Models in
theorem certificate7290 : CFSG.ComponentClassification.J2Cover.Models.oddCheck () = true := CertificateChecks.Batch7290.oddCheck_eq

end Certificates
