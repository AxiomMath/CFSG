module

public import CFSG.Sporadic.HeldB.CertPChainData
public import CFSG.Sporadic.HeldB.CertPFieldsData
import Certificates.Kernel.Sporadic.He.Stab2110

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HeldB in
theorem certificate2110 : (∀ j ∈ heStabIdx, (heStrong j)[0]! = 0) ∧
    (∀ y < 8330, y = 0 ∨ ∃ j ∈ heStabIdx, (heStrong j)[y]! ≠ y) := KernelSpor.HeText.facts

end Certificates
