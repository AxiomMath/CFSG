module

public import Certificates.Kernel.Census.J2V.Pack
public import Certificates.Kernel.Census.J2H.Checks
public import Certificates.Kernel.J2Cover.KerChains
public import Certificates.Data.Kernel.J2V
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelJ2V

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CFSG.KC.J2V
open CertificateChecks.KernelJ2H CertificateChecks.KernelJ2Cover
open CFSG.ComponentClassification.HarrisLit.EndB CFSG.ComponentClassification.J2Cover

@[expose] noncomputable def UP : Nat := pcomp 315 9 (mask 9) (CRT.S 0) (CRT.S 2)

theorem vp_canon : allN 128 (fun k => canonK 315 9 (mask 9) (315 * 9) (VP k)) = true := by
  quickRfl

theorem vp_words : allN 128 (fun k => wA (posW (vWords.getD k [])) (VP k)) = true := by quickRfl

theorem vp_zero : Nat.beq (VP 0) (pidn 315 9) = true := by quickRfl

theorem vp_one : arrBind twoAArr 315 9 (VP 1) = true := by quickRfl

theorem vp_inv : allN 128 (fun i =>
    Nat.beq (pcomp 315 9 (mask 9) (VP i) (VP (tabI vIt i))) (pidn 315 9)) = true := by quickRfl

theorem vp_dist : allN 128 (fun i => allN 128 fun j =>
    Nat.beq i j || !Nat.beq (VP i) (VP j)) = true := by quickRfl

theorem crt_canon : canonK 315 9 (mask 9) (315 * 9) (CRT.S 0) = true ∧
    canonK 315 9 (mask 9) (315 * 9) (CRT.S 2) = true := ⟨by quickRfl, by quickRfl⟩

theorem up_canon : canonK 315 9 (mask 9) (315 * 9) UP = true := by quickRfl

theorem up_conj : allN 128 (fun k =>
    Nat.beq (pcomp 315 9 (mask 9) UP (VP k)) (pcomp 315 9 (mask 9) (VP (tabI vCut k)) UP)) =
    true := by quickRfl

theorem up_sq : Nat.beq (pcomp 315 9 (mask 9) UP UP) (VP vUsqt) = true := by quickRfl

end CertificateChecks.KernelJ2V
