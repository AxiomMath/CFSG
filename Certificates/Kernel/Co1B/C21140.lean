module

public import CFSG.Sporadic.Co1Block.TwoACheckInputs
public import CFSG.Sporadic.Co1Patterson.NativeQInputs
public import Certificates.Kernel.Co1B.Iota
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1Block.Iota

public section

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B

open Certificates in
open CFSG.Sporadic.Co1Block in
theorem c21140 :
    CFSG.Sporadic.Co1Patterson.Native.qExtraOK iotaARows twoAQRows = true := by
  rw [iotaA_eq, twoAQ_eq]
  quickRfl

end CertificateChecks.KernelCo1B

end
