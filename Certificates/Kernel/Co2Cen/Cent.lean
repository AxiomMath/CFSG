module

public import Certificates.Kernel.Co2Cen.Data
public import Certificates.Kernel.Co2J.Data
public import Certificates.Kernel.Co2Syl.Small
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Cen

open CFSG.KC.Co2J CFSG.KC.Co2Cen CertificateChecks.KernelSpor.Co2Syl

theorem jInP1 : jInTK G1 Co2J.GJ JW1 JL1 = true := by quickRfl

theorem coord1 : coordAllK G1 Co2J.GJ Co2J.JE MK1 = true := by quickRfl

theorem fix1 : fixK MK1 F1 4 = true := by quickRfl

theorem aGen : jGenK GA = true := by quickRfl

theorem aEnum : jEnumK GA AE AS = true := by quickRfl

theorem aInP8 : jInTK G8 GA JW8 JL8 = true := by quickRfl

theorem coord8 : coordAllK G8 GA AE MK8 = true := by quickRfl

theorem fix8 : fixK MK8 F8 16 = true := by quickRfl

end CertificateChecks.KernelSpor.Co2Cen

end
