module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzDBridgeCheck
import Certificates.Kernel.Sporadic.OddCore.Suz27140

public section

namespace Certificates

open CertificateChecks

theorem certificate27140 : CFSG.EvenSporadicStandard.Induction.suzDBridgeCheck = true := KernelSpor.SuzD.check27140

end Certificates
