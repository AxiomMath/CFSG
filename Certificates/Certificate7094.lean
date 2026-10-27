module

public import Certificates.Data.RuTypeJ47Inputs
import Certificates.Kernel.Misc.TitsJ47.Final

public section

namespace Certificates

open CertificateChecks

theorem certificate7094 : CFSG.Quasithin.RuType.J47.checkAll = true :=
  KernelMisc.TitsJ47.checkAll_true

end Certificates
