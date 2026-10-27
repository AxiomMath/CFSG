
module

public import Certificates.Data.CatFactsL4U4P1U43Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CentTriv
import Certificates.Kernel.SchreierFam.C22241

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.HarrisLit.P1 CFSG.ComponentClassification.HarrisLit.P1.U43 in
theorem certificate22241 : centTrivOK 820 uSift u43CentTriv = true :=
  KernelSchreierFam.C22241.centTriv

end Certificates
