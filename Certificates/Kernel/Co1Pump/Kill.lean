module

public import Certificates.Data.Kernel.Co1PumpFus
public import Certificates.Data.Kernel.Co1Pairs
public import Certificates.Kernel.Co1Pump.Data
public import Certificates.Kernel.Co1Pairs.Data
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Kernel.Co1SevenK.Dag
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Pump

open CFSG.KC.Co1Pairs CFSG.KD.Co1Pump CertificateChecks.KernelCo1ThreeK
open CFSG.KD.Co1Pairs (R0 R1 R2)

theorem ch36909c3 : conjOK L.M L.MI v3 V3 R1 (R.M 1) = true := by quickRfl
theorem ch36909c6 : conjOK L.M L.MI v6 V6 R2 (R.M 0) = true := by quickRfl
theorem ch36909k0 : eltOK L.M L.MI v0 V0 R0 13 = true := by quickRfl
theorem ch36909k1 : eltOK L.M L.MI v1 V1 R1 7 = true := by quickRfl
theorem ch36909c2 : conjOK L.M L.MI v2 V2 V1 (CertificateChecks.KernelCo1SevenK.D.M 66) = true := by
  quickRfl
theorem ch36909k4 : eltOK L.M L.MI v4 V4 (R.M 2) 7 = true := by quickRfl
theorem ch36909c5 : conjOK L.M L.MI v5 V5 V4 (CertificateChecks.KernelCo1SevenK.D.M 67) = true := by
  quickRfl
theorem ch36909kn : (neK V0 && neK V1 && neK V4) = true := by quickRfl

end CertificateChecks.KernelCo1Pump

end
