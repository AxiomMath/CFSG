module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzOuterData
import Certificates.Kernel.Sporadic.OddCore.Suz27215F

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.SuzOuter in
theorem certificate27215 : suzOuterCheck = true := KernelSpor.S27215.check27215

end Certificates
