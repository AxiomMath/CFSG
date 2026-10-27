module

public import Certificates.Kernel.Misc.OmegaSix.Final

public section

open CFSG.CGT.Foote82.CaseIIClassAux

namespace CertificateChecks.Batch919123

open CFSG.CGT.Foote82.CaseIIClassAux

theorem closureCheck_holds : closureCheck () = true := CFSG.KD.OmegaSix.closureCheck_ok

end CertificateChecks.Batch919123

namespace Certificates

open CertificateChecks

open CFSG.CGT.Foote82.CaseIIClassAux in
theorem certificate919123 : closureCheck () = true :=
  CertificateChecks.Batch919123.closureCheck_holds

end Certificates
