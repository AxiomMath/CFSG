module

public import Certificates.Data.TitsFiveLocal
public import Certificates.Data.MaxD2TI
import Certificates.Kernel.MaxD2.TitsA.Glue
import Certificates.Kernel.MaxD2.TitsA.TI
import CFSG.Certificates.Kernel.MaxD2.TI

public section

namespace Certificates

open CertificateChecks

open CFSG.KS CFSG.KS.MaxD2 CFSG.KS.PEnum CertificateChecks.KernelMaxD2.TitsA

theorem certificate41722 : Certificates.MaxD2TI.checkTI Certificates.MaxD2Perm.titsAData = true := by
  refine checkTI_of hyps fun i h0 hi => ?_
  have hi' : i < 16 := hi
  have h := (PK.allN_iff.1 k_ti) (i - 1) (by omega)
  have e : Nat.succ (i - 1) = i := by omega
  rw [e] at h
  intro hm
  change Nat.mod (r32 CN i) 5 = 0 at hm
  rw [hm] at h
  exact absurd h (by decide)

end Certificates
