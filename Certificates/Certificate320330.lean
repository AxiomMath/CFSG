module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43Data
import Certificates.Kernel.U43Pk.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate320330 : CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check.sylowOK
    CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check.u43Data = true := KernelU43Pk.sylowOK_true

end Certificates
