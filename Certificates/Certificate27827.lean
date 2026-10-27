module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUKsCheck
import Certificates.Kernel.KsEight.SylGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate27827 : CFSG.EvenSporadicStandard.Fin76b.U16.ks8Check () = true ∧
    CFSG.EvenSporadicStandard.Fin76b.U16.ks8Counts () = true :=
  ⟨KernelKsEight.SylG8.ks8Check_true, KernelKsEight.SylG8.ks8Counts_true⟩

end Certificates
