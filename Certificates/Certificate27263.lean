module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYA5S5Data
import Certificates.Kernel.HSStd.A5S5

public section

open CFSG.EvenSporadicStandard.HSStd.FiveY

namespace Certificates

open CertificateChecks

theorem a5s5Stmt_true : a5s5Stmt := KernelHSStd.a5s5Stmt_kernel

theorem certificate27263 : CFSG.EvenSporadicStandard.HSStd.FiveY.a5s5Stmt := a5s5Stmt_true

end Certificates
