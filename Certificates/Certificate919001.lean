module

public import Certificates.Kernel.Misc.OmegaSix.FinalE

public section

open CFSG.CGT.Foote82.OmegaSix

namespace CertificateChecks.Batch919001

open CFSG.CGT.Foote82.OmegaSix

theorem involCheck_holds : involCheck () = true := CFSG.KD.OmegaSix.involCheck_ok

theorem isomCheck_holds : isomCheck () = true := CFSG.KD.OmegaSix.isomCheck_ok

theorem commCheck_holds : commCheck () = true := CFSG.KD.OmegaSix.commCheck_ok

theorem enumCheck_holds : enumCheck () = true := CFSG.KD.OmegaSix.enumCheck_ok

theorem relCheck_holds : relCheck () = true := CFSG.KD.OmegaSix.relCheck_ok

end CertificateChecks.Batch919001

namespace Certificates

open CertificateChecks

open CFSG.CGT.Foote82.OmegaSix in
theorem certificate919001 :
    (involCheck () = true)
    ∧ (isomCheck () = true)
    ∧ (CFSG.CGT.Foote82.OmegaSix.commCheck () = true)
    ∧ (CFSG.CGT.Foote82.OmegaSix.enumCheck () = true)
    ∧ (relCheck () = true) :=
  ⟨CertificateChecks.Batch919001.involCheck_holds, CertificateChecks.Batch919001.isomCheck_holds, CertificateChecks.Batch919001.commCheck_holds,
    CertificateChecks.Batch919001.enumCheck_holds, CertificateChecks.Batch919001.relCheck_holds⟩

end Certificates
