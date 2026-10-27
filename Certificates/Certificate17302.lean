module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Co1SevenOrderFourInputs
public import Certificates.Data.CFSGNative.Co1.Data
import Certificates.Kernel.Co1SevenK.RepsGlue

public section

namespace Certificates

theorem certificate17302 : CFSG.HardMathSupport.Dickson.I271.co1SevenOrderFourOK
    CFSG.Sporadic.Co1.Native.co1Data.rowsA CFSG.Sporadic.Co1.Native.co1Data.rowsB = true :=
  CertificateChecks.KernelCo1SevenK.orderFourOK_K

end Certificates
