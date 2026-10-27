
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSFacts
import Certificates.Kernel.HSDc.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.QuasithinUnique.Ch1.SporLat.HS CFSG.Quasithin.A312S in
theorem certificate4102 : 
    HSLatSpec ∧ HSQuot1Fact ∧ HSInclFact ∧ HSStructFact ∧ HSA1Fact ∧ HSA2Fact :=
  HSF.facts

end Certificates
