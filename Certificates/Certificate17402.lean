module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThThirteenInputs
import Certificates.Kernel.Th.Fam.C17402
import Certificates.Kernel.Th.Fam.Ctx
import CFSG.Certificates.Kernel.Th.ThirteenSound

public section

namespace Certificates

open CertificateChecks

theorem certificate17402 : CFSG.HardMathSupport.Dickson.Sec6.I1431.ThThirteenNative.th13OK () = true :=
  CFSG.KC.Th.Thirteen.th13OK_of KernelTh.Fam.thCtx KernelTh.Fam.ok17402

end Certificates
