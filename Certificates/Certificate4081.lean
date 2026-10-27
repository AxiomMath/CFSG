module

import Certificates.Kernel.SporSch.PairHS.Check2220
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.PairHSCheckInputs

public section

namespace Certificates

open CFSG.KS.SporSch CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.PHSCount in
open CFSG in
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative in
theorem certificate4081 : (PairHS.cl.map (fun c => c.2.1.size) = [5775, 15400]) := by
  have hA : EA.1.size = 5775 :=
    (ClTP.closNFT_proved (bs := CFSG.Sporadic.Schreier.PairHS.bs)
      (rep := CFSG.Sporadic.Schreier.PairHS.wA) PHSCheck.binds PHSCheck.perm PHSC.ho (by decide)
      PHSCheck.tabs rfl PHSCheck.hg PHSCheck.repA_eq PHSCheck.okA).2.1.trans
      (Nat.eq_of_beq_eq_true PHSCl.cASz)
  have hB : EB.1.size = 15400 :=
    (ClTP.closNFT_proved (bs := CFSG.Sporadic.Schreier.PairHS.bs)
      (rep := CFSG.Sporadic.Schreier.PairHS.wC) PHSCheck.binds PHSCheck.perm PHSC.ho (by decide)
      PHSCheck.tabs rfl PHSCheck.hg PHSCheck.repB_eq PHSCheck.okB).2.1.trans
      (Nat.eq_of_beq_eq_true PHSCl.cBSz)
  change [EA.1.size, EB.1.size] = [5775, 15400]
  rw [hA, hB]

end Certificates
