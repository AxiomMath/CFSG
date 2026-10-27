module

public import Certificates.Data.Co1FiveComp
public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
import Certificates.Kernel.Co1FiveComp.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate10145 : Timmesfeld.Co1FiveComp.compOK CFSG.Sporadic.Co1Schreier.Native.aR
    CFSG.Sporadic.Co1Schreier.Native.bR = true :=
  KernelCo1FiveComp.compOK_eq_true

end Certificates
