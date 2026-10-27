module

public import Certificates.Kernel.D4.Tabs
public import Certificates.Kernel.D4.EnumA
public import Certificates.Kernel.D4.EnumB
public import Certificates.Data.Kernel.D4WordPos
public import Certificates.Data.Fam3D42Local

public section

namespace CertificateChecks.KernelD4

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.D4Local
open CFSG.HardMathSupport.Dickson.Bal207.Fam3D42

theorem uA_ok : uFlagK 2457 12 (LX 0) (pw 2457 12 (LX 0) 2) (wordPos 2457 12 EA.G uWordA) =
    true := by
  decide +kernel

theorem uB_ok : uFlagK 2457 12 (LX 1) (pw 2457 12 (LX 1) 2) (wordPos 2457 12 EB.G uWordB) =
    true := by
  decide +kernel

end CertificateChecks.KernelD4
