module

public import CFSG.Quasithin.Background.Asc81cPfCheckT
import Certificates.Kernel.Misc.Asc81c.GlueT

public section

namespace Certificates

open CertificateChecks

theorem certificate7226 : CFSG.Quasithin.Asc81c.Pf.Check.checkT 4 = true ∧
    CFSG.Quasithin.Asc81c.Pf.Check.checkT 3 = true := KernelAsc81c.c7226

end Certificates
