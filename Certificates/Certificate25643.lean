module

public import CFSG.Monster.B.Fischer.Fi22Graph
public import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
import Certificates.Certificate2067
import Certificates.Certificate3039
import Certificates.Certificate3147
import Certificates.Kernel.Sporadic.Fi22.HypCBGlue
import Certificates.Kernel.Sporadic.Fi22.C2068

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.ComponentClassification.M12Cover in
open CFSG.Sporadic.Schreier in
theorem certificate25643 : FourClassesLarge ↥(CFSG.Sporadic.Schreier.centralizerIn fi22P (fi22ExtRep 2)) := KernelSpor.Fi22CB.fourClassesLarge_CP2

end Certificates
