module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusDataA
import Certificates.Kernel.GHarrisFus.Glue

public section

namespace Certificates

open CertificateChecks.KernelGHarrisFus in
open CFSG.ComponentClassification.GHarris.SCert in
theorem certificate22608 : SE.clsOk = true ∧ Fus.checkList [Fus.aZ] = true ∧ Fus.checkList [Fus.aT] = true ∧
    Fus.checkList [Fus.aA1L] = true ∧ Fus.checkList [Fus.aA34] = true :=
  ⟨glue22608_clsOk, glue22608_aZ, glue22608_aT, glue22608_aA1L, glue22608_aA34⟩

end Certificates
