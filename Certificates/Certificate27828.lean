
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUKs2Check
import Certificates.Kernel.Ks2.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate27828 : CFSG.EvenSporadicStandard.Fin76b.U16.u7Check () = true ∧
    CFSG.EvenSporadicStandard.Fin76b.U16.pairCheck () = true ∧
    CFSG.EvenSporadicStandard.Fin76b.U16.d16Check () = true :=
  ⟨KernelKs2.G.u7Check_true, KernelKs2.G.pairCheck_true, KernelKs2.G.d16Check_true⟩

end Certificates
