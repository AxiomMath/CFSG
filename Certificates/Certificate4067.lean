module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Data
import Certificates.Kernel.J2Cover.Tab4067
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2Inputs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 in
theorem certificate4067 : (j2Data.ta.toList = CFSG.QuasithinUnique.K1.SporadicPerm.j2ta)
    ∧ (j2Data.tb.toList = CFSG.QuasithinUnique.K1.SporadicPerm.j2tb) := KernelJ2Cover.Tab.facts

end Certificates
