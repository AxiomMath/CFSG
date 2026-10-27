module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGData
import Certificates.Kernel.TwoHSLe4.Stage1Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate27230 : PGStage1F := KernelTwoHSLe4.SO5.stage1

end Certificates
