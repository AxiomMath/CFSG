module

public import CFSG.LocalAnalysis.OddStandard.ONanB2Facts
import Certificates.Kernel.ONanB2.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.ONanRec.CM in
theorem certificate6149 : B2Facts ∧ B2Chain :=
  ⟨ONanB2.b2_facts, ONanB2.b2_chain⟩

end Certificates
