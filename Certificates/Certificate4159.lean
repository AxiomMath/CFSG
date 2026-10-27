module

public import Certificates.Data.U43NoL3
public import CFSG.LieType.Multipliers.U43Data
import Certificates.Kernel.U43Cls.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.KGroups.U43 CFSG.LieType.Multipliers.U43 in
theorem certificate4159 : noSevenCheck 820 CFSG.LieType.Multipliers.U43.tabA CFSG.LieType.Multipliers.U43.tabB = true := KernelU43Cls.noSeven_ok

end Certificates
