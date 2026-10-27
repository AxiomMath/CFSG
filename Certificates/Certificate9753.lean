module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Check
public import CFSG.GH74.KGroups.L33Inputs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.KGroupsE.K9753

public section

namespace Certificates

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

theorem certificate9753 : CFSG.CGT.PushingUpLit.SolKNA.R4.Check.noQ16Check
    (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.L33.QA)
    (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
      (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.L33.QA)) = true :=
  by simp only [elemsT_eq_elemsV]; exact q16_9753K

end Certificates
