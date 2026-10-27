module

public import Certificates.Data.CFSGNative.Timmesfeld.Co1Seven
public import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Timmesfeld.Co1Seven
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.TwoB
import Certificates.Kernel.Co1SevenK.SylGlue

public section

namespace Certificates

theorem certificate13696 : Timmesfeld.Co1Seven.sylowOK
    CFSG.Sporadic.Co1.Native.co1Data.rowsA
    CFSG.Sporadic.Co1.Native.co1Data.rowsB = true :=
  CertificateChecks.KernelCo1SevenK.sylowOK_K

end Certificates
