module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43Data
import Certificates.Kernel.U43Pk.CovFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate320331 : CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check.coverOK
    CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check.u43Data = true := KernelU43Pk.coverOK_true

end Certificates
