module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCJ3Check
import Certificates.Kernel.Sporadic.OddCore.J3OutSylF

public section

namespace Certificates

open CertificateChecks

theorem certificate25510 : CFSG.EvenSporadicStandard.Fin76b.J3.j3OuterCheck = true := KernelSpor.J3OutSyl.facts25510

end Certificates
