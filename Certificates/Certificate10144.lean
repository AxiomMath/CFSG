module

public import Certificates.Data.Co1SevenPerfect
public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
import Certificates.Kernel.Co1SevenK.PerfGlue

public section

namespace Certificates

theorem certificate10144 : Timmesfeld.Co1SevenPerfect.co1PerfOK CFSG.Sporadic.Co1Schreier.Native.aR
    CFSG.Sporadic.Co1Schreier.Native.bR = true :=
  CertificateChecks.KernelCo1SevenK.co1PerfOK_K

end Certificates
