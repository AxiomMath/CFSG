module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGData
import Certificates.Kernel.TwoHSLe4.Chi

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate27231 : PGChiF := KernelTwoHSLe4.Chi.chi

end Certificates
