module

public import Certificates.Kernel.Co1P.Defs21150S
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Co1PText
public import Certificates.Kernel.Co1P.Defs21150
public import Certificates.Kernel.Co1P.Defs21151
public import Certificates.Kernel.Co1P.Defs21154

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Patterson.Native

theorem closQ_ok : closQ = true := by quickRfl

theorem th4_ok : allN 43 th4_chunk = true := by quickRfl

theorem bk_inv : andB (Nat.beq (lenL BK) 8) (invsOK BK BIK) = true := by quickRfl

theorem dag_inv : dagInvK = true := by quickRfl

end CertificateChecks.KernelCo1P

end
