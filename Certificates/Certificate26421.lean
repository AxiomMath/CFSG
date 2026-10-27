module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Fin
import Certificates.Kernel.TwoHSLe4.NormGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26421 : NormComplete := KernelTwoHSLe4.Norm.normComplete

end Certificates
