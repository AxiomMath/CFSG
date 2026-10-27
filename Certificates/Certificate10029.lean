module

import Certificates.Kernel.Co1M.C10029
public import CFSG.Sporadic.Co1.Module.CoTwoDataInputs
public import CFSG.Sporadic.Co1.Module.CoTwoNortonDataInputs

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1.Module.CoTwo in
theorem certificate10029 :
    (rrA 13 = r1Rows)
    ∧ (rrA 18 = r2Rows) := KernelCo1M.c10029

end Certificates
