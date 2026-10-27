module

public import CFSG.Quasithin.Background.Harris.R1.J2VertCheck
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
import Certificates.Kernel.J2Vert.Nonsplit300202Facts
public import CFSG.Quasithin.Background.Harris.R1.J2VertTables

public section

namespace Certificates

open CFSG.Quasithin.Background.Harris.R1.J2Vert CFSG.ComponentClassification.J2Cover in
theorem certificate300202 :
    (relCheck 315 (rGenArrs 315 #[autStrong[0]!, autStrong[1]!, outerArr]) (vRels true) = true)
    ∧ (tabLower 315 (rGenArrs 315 #[autStrong[0]!, autStrong[1]!, outerArr]) tabR 3840 = true) :=
  CertificateChecks.KernelJ2Vert.Nonsplit.facts

end Certificates
