module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusDataB
import Certificates.Kernel.GHarrisFus.Glue

public section

namespace Certificates

open CertificateChecks.KernelGHarrisFus in
open CFSG.ComponentClassification.GHarris.SCert in
theorem certificate22609 :
    Fus.checkList [Fus.yIZ] = true ∧
    Fus.checkList [Fus.yIX] = true ∧
    Fus.checkList [Fus.bIZ] = true ∧
    Fus.checkList [Fus.bIA1L] = true ∧
    Fus.checkList [Fus.bIX] = true ∧
    Fus.checkList [Fus.bIIZ] = true ∧
    Fus.checkList [Fus.bIIA1L] = true ∧
    Fus.checkList [Fus.bIIX] = true ∧
    Fus.checkList [Fus.bIIA34] = true ∧
    Fus.checkList [Fus.yIIZ] = true ∧
    Fus.checkList [Fus.yIIA34] = true ∧
    Fus.checkList [Fus.yIIX] = true :=
  ⟨glue22609_yIZ, glue22609_yIX, glue22609_bIZ, glue22609_bIA1L, glue22609_bIX, glue22609_bIIZ,
    glue22609_bIIA1L, glue22609_bIIX, glue22609_bIIA34, glue22609_yIIZ, glue22609_yIIA34,
    glue22609_yIIX⟩

end Certificates
