module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGCore
import Certificates.Kernel.TwoHSLe4.CoreGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate27232 : PGCoreF := KernelTwoHSLe4.SO5.core

end Certificates
