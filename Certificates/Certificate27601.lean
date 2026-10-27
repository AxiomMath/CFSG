module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10Data
import Certificates.Kernel.U43Rho.M10Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate27601 : CFSG.EvenSporadicStandard.M24Std.CU43.rhoCheck = true ∧
    CFSG.EvenSporadicStandard.M24Std.CU43.order6Check = true :=
  ⟨KernelU43Rho.rhoCheck_K, KernelU43Rho.order6Check_K⟩

end Certificates
