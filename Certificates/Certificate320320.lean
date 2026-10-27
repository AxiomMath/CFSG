module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocL43Data
import Certificates.Kernel.LocL43.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate320320 : CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc.locCheck 4
    CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc.inF4
    CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc.l43Data = true := KernelLocL43.check_true

end Certificates
