module

public import Certificates.Data.Kernel.Co1Pairs
public import Certificates.Kernel.Co1Pairs.Data
public import Certificates.Kernel.Co1ThreeK.Letters
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Pairs

open CFSG.KC.Co1Pairs CFSG.KD.Co1Pairs CertificateChecks.KernelCo1ThreeK

theorem ch214033e0 : eltOK L.M L.MI w0 K0 R0 7 = true := by quickRfl
theorem ch214033e1 : eltOK L.M L.MI w1 K1 R0 7 = true := by quickRfl
theorem ch214033e2 : eltOK L.M L.MI w2 K2 R1 7 = true := by quickRfl
theorem ch214033e3 : eltOK L.M L.MI w3 K3 R1 7 = true := by quickRfl
theorem ch214033e4 : eltOK L.M L.MI w4 K4 R2 5 = true := by quickRfl
theorem ch214033e5 : eltOK L.M L.MI w5 K5 R2 5 = true := by quickRfl
theorem ch214033e6 : eltOK L.M L.MI w6 K6 (R.M 2) 7 = true := by quickRfl
theorem ch214033e7 : eltOK L.M L.MI w7 K7 (R.M 2) 7 = true := by quickRfl
theorem ch36909u8 : eltOK L.M L.MI w8 K8 R2 5 = true := by quickRfl
theorem ch36909u9 : eltOK L.M L.MI w9 K9 R2 5 = true := by quickRfl

theorem ch214033p : prodOK K0 K1 13 = true := by quickRfl

end CertificateChecks.KernelCo1Pairs

end
