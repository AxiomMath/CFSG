module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rank
import Certificates.Kernel.Sporadic.Co2.HypGlue
public import CFSG.Sporadic.Co2Schreier.ThirdOrderBase

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier CFSG.ComponentClassification.M12Cover in
open CFSG.Sporadic.Schreier CFSG.EvenSporadicStandard.HypOne in
theorem certificate24446 : FourClassesLarge ↥(centralizerIn co2P locU) ∧ HasElemAbelianEight ↥co2P :=
  ⟨KernelSpor.Co2HG.fourClassesLarge_u, KernelSpor.Co2HG.hasElemAbelianEight_co2P⟩

end Certificates
