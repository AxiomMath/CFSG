
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Facts
import Certificates.Kernel.M24Dc.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.QuasithinUnique.Ch1.SporLat.M24 in
theorem certificate4068 : 
    M24LatSpec ∧ M24InclFact ∧ M24Idx3Fact ∧ M24CenFact ∧ M24E64Fact ∧ M24T3J4Fact ∧ M24KGFact :=
  M24F.facts

end Certificates
