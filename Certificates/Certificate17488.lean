module

public import Certificates.Data.TabMSevenCo1Reps
public import Certificates.Data.CFSGNative.Co1.Data
import Certificates.Kernel.Co1SevenK.RepsGlue

public section

namespace Certificates

theorem certificate17488 : CFSG.HardMathSupport.Dickson.I271.TabMSeven.sevenRepsOK
    CFSG.Sporadic.Co1.Native.co1Data.rowsA CFSG.Sporadic.Co1.Native.co1Data.rowsB = true :=
  CertificateChecks.KernelCo1SevenK.sevenRepsOK_K

end Certificates
