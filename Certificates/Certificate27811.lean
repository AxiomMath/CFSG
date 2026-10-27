module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYF1Check
import Certificates.Kernel.Sporadic.OddCore.F1K27811
import Certificates.Kernel.Sporadic.OddCore.J2CnF
import Certificates.Kernel.Sporadic.OddCore.J3PGGlue
import Certificates.Kernel.SporSch.J3K426.Sift

namespace CertificateChecks.Batch27811

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PkPow CFSG.KC.BfsPin CFSG.KS.MulH
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Monster.B.Co2.Native CFSG.EvenSporadicStandard.Fin76b.S16 CFSG.Sporadic.Schreier.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.F27811

theorem strictN_id (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_id (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem pows (n w P : Nat) : Pows n w P (ppw n w P) :=
  ⟨rfl, fun e => strictN_id (ppw n w P e) (fun q => pcomp n w (mask w) P q)⟩

theorem not_of_bIf {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

theorem f1_of {n w t r u : Nat} {sr su : Bool} {sift : Table → Bool} (hn : n < 2 ^ 32)
    (h : f1K n w t r u sr su = true) (ht : permOK n (tabT (unpack n w t)) = true)
    (hsr : sr = true → sift (tabT (unpack n w r)) = true)
    (hsu : su = true → sift (tabT (unpack n w u)) = true) :
    f1Check n sift (tabT (unpack n w t)) (tabT (unpack n w r)) (tabT (unpack n w u)) = true := by
  unfold f1K at h
  rw [strictB_id] at h
  simp only [bAnd_iff] at h
  obtain ⟨hsz, hci, hct, hcr, hcu, hcri, hir, hiu, sr', su', crt, cut, r8, r4, uu, uru, hall⟩ := h
  have hid : idT n = tabT (unpack n w (pidn n w)) := by rw [idT_tabT, idA_eq hsz]
  have pw := powT_unpack (pows n w r) hid hci hcr
  have te : ∀ e, tblEq n (tabT (unpack n w u)) (tabT (unpack n w (ppw n w r e))) =
      Nat.beq u (ppw n w r e) := fun e => tblEq_unpack hcu (pows_canon (pows n w r) hci hcr e)
  have hn' : n < 4294967296 := hn
  unfold f1Check
  rw [invoOK_eq' hn, invT_unpack hn' hir, compT_unpack hcu hcr,
    compT_unpack (canonK_pcomp hcu hcr) hcu, compT_unpack hcu hcu, pw 8, pw 4, hid,
    commTT_unpack hcr hct, commTT_unpack hcu hct,
    tblEq_unpack (pows_canon (pows n w r) hci hcr 8) hci,
    tblEq_unpack (pows_canon (pows n w r) hci hcr 4) hci, tblEq_unpack (canonK_pcomp hcu hcu) hci,
    tblEq_unpack (canonK_pcomp (canonK_pcomp hcu hcr) hcu) hcri]
  simp only [pw, te]
  simp only [ht, permOK_unpack hcr hir, permOK_unpack hcu hiu, hsr sr', hsu su', crt, cut, r8,
    not_of_bIf r4, uu, invOK_unpack hcr hcri hir, uru, hall, Bool.not_false, Bool.and_self]

theorem f1K_canon {n w t r u : Nat} {sr su : Bool} (h : f1K n w t r u sr su = true) :
    canonK n w (mask w) (n * w) r = true ∧ canonK n w (mask w) (n * w) u = true := by
  unfold f1K at h
  rw [strictB_id] at h
  simp only [bAnd_iff] at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1⟩

theorem j2Tb_eq {k : Nat} (hk : k < 14) : j2Tb k = tabT (unpack 315 9 (TS16J2T.F k)) := by
  have h : natArr (j2Tb k) = unpack 315 9 (TS16J2T.F k) := by
    have h := CFSG.KC.Misc.HexFlat.hexT_sound TS16J2T.all (by norm_num) k hk
    rw [← TS16J2T.eq] at h
    exact h
  rw [← tabT_natArr (j2Tb k), h]

theorem j3Tb_eq {k : Nat} (hk : k < 13) : j3Tb k = tabT (unpack 6156 13 (TS16J3P k)) := by
  have h : natArr (j3Tb k) = unpack 6156 13 (TS16J3P k) := by
    have h := CFSG.KS.Join.hexT_join_sound (d := 4) (n₀ := 513) (w := 13) (c := 12) (N := 13)
      TS16J3T.all ts16_join (by norm_num) k hk
    rw [← TS16J3T.eq] at h
    exact h
  rw [← tabT_natArr (j3Tb k), h]

theorem j2 : j2F1OK = true := by
  unfold j2F1OK
  rw [J2Cn.tabF (by norm_num), j2Tb_eq (by norm_num), j2Tb_eq (by norm_num)]
  refine f1_of (by norm_num) k27811_j2 ?_ ?_ ?_
  · rw [← J2Cn.tabF (by norm_num)]
    exact J2Cn.permF (by norm_num)
  · intro h
    rw [J2Cn.sift_eq (f1K_canon k27811_j2).1]
    exact h
  · intro h
    rw [J2Cn.sift_eq (f1K_canon k27811_j2).2]
    exact h

theorem j3sift {wd : List Int} {P : Nat} (hc : canonK 6156 13 (mask 13) (6156 * 13) P = true)
    (h : j3W wd P = true) : j3Sift (tabT (unpack 6156 13 P)) = true := by
  unfold j3Sift
  rw [natArr_tabT hc]
  exact CertificateChecks.KernelSporSch.J3KT.sift_of h

theorem j3 : j3F1OK = true := by
  unfold j3F1OK
  rw [OddCore.J3W.t_eq, j3Tb_eq (by norm_num), j3Tb_eq (by norm_num)]
  have hc := f1K_canon k27811_j3
  refine f1_of (by norm_num) k27811_j3 ?_ (j3sift hc.1) (j3sift hc.2)
  rw [← OddCore.J3W.t_eq]
  exact OddCore.J3W.perm_t

end CertificateChecks.Batch27811

public section

namespace Certificates

open CertificateChecks

theorem certificate27811 : CFSG.EvenSporadicStandard.Fin76b.S16.j2F1OK = true ∧
    CFSG.EvenSporadicStandard.Fin76b.S16.j3F1OK = true :=
  ⟨CertificateChecks.Batch27811.j2, CertificateChecks.Batch27811.j3⟩

end Certificates
