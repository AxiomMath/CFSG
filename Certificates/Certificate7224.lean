module

public import CFSG.Quasithin.Background.Asc81cPfCheck
import Certificates.Kernel.Misc.Asc81c.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate7224 : CFSG.Quasithin.Asc81c.Pf.Check.check4 = true ∧
    CFSG.Quasithin.Asc81c.Pf.Check.check3 = true := KernelAsc81c.c7224

end Certificates
