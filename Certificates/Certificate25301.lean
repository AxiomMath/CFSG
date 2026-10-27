module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeCheck
import Certificates.Kernel.LocalComp.Fi24TwoB.Shape25301

public section

namespace Certificates

open CertificateChecks

theorem certificate25301 : CFSG.EvenSporadicStandard.TwoFi22.DS81.fi24ShapeCheck = true := KernelLC.Fi24Shape.check

end Certificates
