module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocL53Data
import Certificates.Kernel.LocL53.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate320321 : CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc.locCheck 5
    CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc.inF5
    CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc.l53Data = true := KernelLocL53.check_true

end Certificates
