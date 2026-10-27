module

public import Certificates.Kernel.Misc.OmegaSix.FinalO

public section

open CFSG.CGT.Foote82.CaseIIClassAux

namespace CertificateChecks.Batch919122

open CFSG.CGT.Foote82.CaseIIClassAux

theorem reflOrbitCheck_holds : reflOrbitCheck () = true := CFSG.KD.OmegaSix.reflOrbitCheck_ok

theorem a6Check_holds : a6Check () = true := CFSG.KD.OmegaSix.a6Check_ok

theorem a6CentCheck_holds : a6CentCheck () = true := CFSG.KD.OmegaSix.a6CentCheck_ok

end CertificateChecks.Batch919122

namespace Certificates

open CertificateChecks

open CFSG.CGT.Foote82.CaseIIClassAux in
theorem certificate919122 :
    (reflOrbitCheck () = true)
    ∧ (CFSG.CGT.Foote82.CaseIIClassAux.a6Check () = true)
    ∧ (a6CentCheck () = true) :=
  ⟨CertificateChecks.Batch919122.reflOrbitCheck_holds, CertificateChecks.Batch919122.a6Check_holds,
    CertificateChecks.Batch919122.a6CentCheck_holds⟩

end Certificates
