module

public import Certificates.Kernel.Co2Census.TInvData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2TInv

open CFSG.KC.Co2TInv CertificateChecks.KernelSpor.Co2J

theorem lift : liftAllK G MK PE JE CL LW LN LT SC 15 = true := by quickRfl

theorem scan : scanAllK PE CL SC RR RN SW 15 = true := by quickRfl

theorem fus : fusCK PE INV CL FU 15 71 = true := by quickRfl

theorem jorb : jorbK PE JR JO 31 = true := by quickRfl

end CertificateChecks.KernelSpor.Co2TInv

end
