module

public import Certificates.Data.GrSLitL34HeldCenterCheck
import Certificates.Kernel.HeLoc.FiveFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34HeldCenter in
theorem certificate22221 : heFiveNoFourOK = true := KernelHeLoc.Five.noFour

end Certificates
