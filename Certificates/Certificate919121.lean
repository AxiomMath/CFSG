module

public import Certificates.Kernel.Misc.OmegaSix.FinalC

public section

open CFSG.CGT.Foote82.CaseIIClassAux

namespace CertificateChecks.Batch919121

open CFSG.CGT.Foote82.CaseIIClassAux

theorem omClassCheck_holds : omClassCheck () = true := CFSG.KD.OmegaSix.omClassCheck_ok

theorem centCountCheck_holds : centCountCheck () = true := CFSG.KD.OmegaSix.centCountCheck_ok

end CertificateChecks.Batch919121

namespace Certificates

open CertificateChecks

open CFSG.CGT.Foote82.CaseIIClassAux in
theorem certificate919121 :
    (omClassCheck () = true)
    ∧ (centCountCheck () = true) :=
  ⟨CertificateChecks.Batch919121.omClassCheck_holds, CertificateChecks.Batch919121.centCountCheck_holds⟩

end Certificates
