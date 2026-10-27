module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWClsCheck
import Certificates.Kernel.Census.W16.Del

public section

namespace Certificates

theorem certificate27822 : CFSG.EvenSporadicStandard.Fin76b.W16.x45Check = true ∧
    CFSG.EvenSporadicStandard.Fin76b.W16.zetaCheck = true ∧
    CFSG.EvenSporadicStandard.Fin76b.W16.twistCheck = true ∧
    CFSG.EvenSporadicStandard.Fin76b.W16.fusCheck = true :=
  ⟨Kernel.CensusW16.x45_ok, Kernel.CensusW16.zeta_ok, Kernel.CensusW16.twist_ok,
    Kernel.CensusW16.fus_ok⟩

end Certificates
