module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.McLCheck
import Certificates.Kernel.Sporadic.OddCore.C129020
import Certificates.Kernel.Sporadic.OddCore.MNF

namespace CertificateChecks.Batch129020

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore CertificateChecks.KernelSpor.MNd
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

theorem heisT {k : Nat} (hk : k < 4) : mclHeisTbl k = tabT (unpack 275 9 (MHeis.F k)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound MHeis.all (by norm_num) k hk
  rw [← MHeis.eq] at h
  unfold mclHeisTbl
  rw [← h, tabT_natArr]

theorem false_of_bIf {c : Bool} (h : bIf(c, false, true) = true) : c = false := by
  cases c
  · rfl
  · exact absurd h Bool.false_ne_true

theorem okc {c X Y T : Nat} (hx : mclHeisTbl (2 * c) = tabT (unpack 275 9 X))
    (hy : mclHeisTbl (2 * c + 1) = tabT (unpack 275 9 Y))
    (ht : mclHeisTau c = tabT (unpack 275 9 T)) (hT : canonK 275 9 (mask 9) (275 * 9) T = true)
    (h : heisK X Y T = true) : mclHeisOK c = true := by
  unfold heisK invPK at h
  rw [CFSG.KS.PEnum.strictB_app', CFSG.KS.PEnum.strictB_app', CFSG.KS.PEnum.strictB_app'] at h
  simp only [bAnd_iff] at h
  obtain ⟨⟨cx, cxi, ix⟩, ⟨cy, cyi, iy⟩, sx, sy, x5, y5, w5, w1, cxw, cyw, inv⟩ := h
  have cW := canonK_pcomp (canonK_pcomp (canonK_pcomp cxi cyi) cx) cy
  have x5' : Nat.beq (pw 5 X) (pidn 275 9) = true := x5
  have y5' : Nat.beq (pw 5 Y) (pidn 275 9) = true := y5
  have w5' : Nat.beq (pw 5 (pcomp 275 9 (mask 9) (pcomp 275 9 (mask 9) (pcomp 275 9 (mask 9)
    (pinvS 275 9 (mask 9) X) (pinvS 275 9 (mask 9) Y)) X) Y)) (pidn 275 9) = true := w5
  have w1' : Nat.beq (pcomp 275 9 (mask 9) (pcomp 275 9 (mask 9) (pcomp 275 9 (mask 9)
    (pinvS 275 9 (mask 9) X) (pinvS 275 9 (mask 9) Y)) X) Y) (pidn 275 9) = false :=
    false_of_bIf w1
  unfold mclHeisOK mclHeisW
  simp only []
  rw [hx, hy, ht, invT_unpack (by norm_num) ix, invT_unpack (by norm_num) iy,
    permOK_unpack cx ix, permOK_unpack cy iy, invOK_unpack cx cxi ix, invOK_unpack cy cyi iy,
    sift_eq cx, sift_eq cy, sx, sy, compT_unpack cxi cyi, compT_unpack (canonK_pcomp cxi cyi) cx,
    compT_unpack (canonK_pcomp (canonK_pcomp cxi cyi) cx) cy, powT_unpack (pows X) hid hidc cx,
    powT_unpack (pows Y) hid hidc cy, powT_unpack (pows _) hid hidc cW, hid,
    tblEq_unpack (canonP cx 5) hidc, tblEq_unpack (canonP cy 5) hidc,
    tblEq_unpack (canonP cW 5) hidc, tblEq_unpack cW hidc, commTT_unpack cx cW,
    commTT_unpack cy cW, compT_unpack hT cx, compT_unpack (canonK_pcomp hT cx) hT,
    tblEq_unpack (canonK_pcomp (canonK_pcomp hT cx) hT) cxi]
  rw [x5', y5', w5', w1']
  change (true && true && true && true && true && true && true && true && true && !false &&
    commK X _ && commK Y _ && Nat.beq (pc (pc T X) T) (pinvS 275 9 (mask 9) X)) = true
  have cxw' : MNd.commK X (pcomp 275 9 (mask 9) (pcomp 275 9 (mask 9) (pcomp 275 9 (mask 9)
    (pinvS 275 9 (mask 9) X) (pinvS 275 9 (mask 9) Y)) X) Y) = true := cxw
  have cyw' : MNd.commK Y (pcomp 275 9 (mask 9) (pcomp 275 9 (mask 9) (pcomp 275 9 (mask 9)
    (pinvS 275 9 (mask 9) X) (pinvS 275 9 (mask 9) Y)) X) Y) = true := cyw
  rw [cxw', cyw', inv]
  rfl

theorem holds : mclHeisCheck () = true := by
  have h := ok129020
  rw [bAnd_iff] at h
  have t0 : mclHeisTau 0 = tabT (unpack 275 9 (S 0)) := by
    rw [mclHeisTau, if_pos rfl]
    exact (pg_tabs.2 0 (by norm_num)).1
  have t1 : mclHeisTau 1 = tabT (unpack 275 9 (F 17)) := by
    rw [mclHeisTau, if_neg (by norm_num)]
    exact tabF (by norm_num)
  unfold mclHeisCheck
  rw [permF (k := 17) (by norm_num),
    okc (heisT (k := 2 * 0) (by norm_num)) (heisT (k := 2 * 0 + 1) (by norm_num)) t0
      (pg_tabs.2 0 (by norm_num)).2 h.1,
    okc (heisT (k := 2 * 1) (by norm_num)) (heisT (k := 2 * 1 + 1) (by norm_num)) t1
      (Fc (by norm_num)) h.2]
  rfl

end CertificateChecks.Batch129020

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic in
theorem certificate129020 : mclHeisCheck () = true := CertificateChecks.Batch129020.holds

end Certificates
