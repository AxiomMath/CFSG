module

public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Facts
import Certificates.Kernel.PermCent.U43P1Main

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.HarrisLit.P1 CFSG.LieType.Multipliers.U43 in
theorem certificate22243 : P1ModelFacts X₀ :=
  KernelPermCent.U43P1.p1ModelFacts_u43K

end Certificates
