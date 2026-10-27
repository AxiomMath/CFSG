module

public import CFSG.LieType.Multipliers.U43Kernel
import Certificates.Kernel.Multipliers.U43Upper

public section

namespace Certificates

open CertificateChecks

open CFSG.LieType.Multipliers.U43 in
theorem certificate10013 : zk 5 ^ 3 = 1 ∧ zk 6 ^ 12 = 1 ∧ zk 0 = zk 6 ^ 6 ∧ zk 1 = 1 ∧ zk 2 = 1 ∧
    zk 3 = zk 6 ^ 6 ∧ zk 4 = zk 6 ^ 3 := KernelU43.kernel_relations

end Certificates
