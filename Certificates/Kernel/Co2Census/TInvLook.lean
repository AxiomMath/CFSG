module

public import Certificates.Kernel.Co2Census.TInvData
public import Certificates.Kernel.Co2Census.TInvCls
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2TInv

open CFSG.KC.Co2TInv CertificateChecks.KernelSpor.Co2J

theorem look : lookAllK CFS NCS JE LT RR RN LK 15 = true := by quickRfl

theorem lookJ : lookJK CFS NCS JE JR JK 31 = true := by quickRfl

end CertificateChecks.KernelSpor.Co2TInv

end
