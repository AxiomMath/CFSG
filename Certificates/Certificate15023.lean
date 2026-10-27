module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuEndK
import Certificates.Kernel.SporSch.Ru.EndK
import Certificates.Kernel.SporSch.Ru.EndEl

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Ru in
theorem certificate15023 : RuEndFactsK :=
  KernelSporSch.RuEnd.ruEndFactsK_of KernelSporSch.RuEndEl.all

end Certificates
