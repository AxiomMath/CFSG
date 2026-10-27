module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWCheck
import Certificates.Kernel.Census.Pg.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate27820 : CFSG.EvenSporadicStandard.Fin76b.W16.tableCheck = true ∧
    CFSG.EvenSporadicStandard.Fin76b.W16.autCheck = true ∧
    CFSG.EvenSporadicStandard.Fin76b.W16.chainCheck = true ∧
    CFSG.EvenSporadicStandard.Fin76b.W16.genCheck = true ∧
    CFSG.EvenSporadicStandard.Fin76b.W16.candCheck = true :=
  KernelPg.cert27820

end Certificates
