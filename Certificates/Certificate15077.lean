
module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusInputs
import Certificates.Kernel.LocalComp.Census.Check

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15077 : CFSG.ComponentClassification.AS81.Census.censusCheck = true :=
  KernelLC.CensusC.census_ok

end Certificates

end
