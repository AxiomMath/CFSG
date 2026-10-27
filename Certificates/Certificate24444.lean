module

public import CFSG.Sporadic.Co2Schreier.Defs
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
import Certificates.Certificate2060
import Certificates.Certificate3115
import Certificates.Certificate3117
import Certificates.Kernel.Sporadic.Co2.HypGlue
public import CFSG.Certificates.InvariantMerge

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier CFSG.ComponentClassification.M12Cover in
open CFSG.Sporadic.Schreier in
theorem certificate24444 : FourClassesLarge ↥(CFSG.Sporadic.Schreier.centralizerIn co2P locZ) :=
  KernelSpor.Co2HG.fourClassesLarge_z

end Certificates
