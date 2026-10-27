module

public import CFSG.Sporadic.Co1.Module.LeechOddLitInputs
import Certificates.Kernel.Co1M.C10071Y
public import Certificates.Kernel.Co1M.C10071

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1.Module.Odd in
theorem certificate10071 :
    (noTwoOK = true)
    ∧ zOneLitOK
    ∧ (coverOK = true)
    ∧ (zTwoLitOK ∧ orbitYLitOK = true)
    ∧ (tripleOK = true)
    ∧ (outerLitOK = true) :=
  ⟨KernelCo1M.c71_noTwo, KernelCo1M.c71_zOne, KernelCo1M.c71_cover,
    ⟨KernelCo1M.c71_zTwo, KernelCo1M.c71_orbitY⟩, KernelCo1M.c71_triple, KernelCo1M.c71_outer⟩

end Certificates
