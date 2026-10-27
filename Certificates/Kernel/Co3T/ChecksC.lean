module

public import Certificates.Kernel.Co3T.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co3T.EnumQ

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3T

theorem kC0 : classB 0 = true := by quickRfl
theorem kC1 : classB 504 = true := by quickRfl
theorem kC2 : classB 1008 = true := by quickRfl
theorem kC3 : classB 1512 = true := by quickRfl
theorem kC4 : classB 2016 = true := by quickRfl
theorem kC5 : classB 2520 = true := by quickRfl
theorem kC6 : classB 3024 = true := by quickRfl
theorem kC7 : classB 3528 = true := by quickRfl
theorem kC8 : classB 4032 = true := by quickRfl

end CertificateChecks.KernelCo3T

end
