module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J3Check
import Certificates.Kernel.Sporadic.OddCore.J3HypSylF

public section

namespace Certificates

open CertificateChecks

theorem certificate24591 : CFSG.EvenSporadicStandard.Fin76b.J3.j3CenterCheck = true := KernelSpor.J3HypSyl.facts24591

end Certificates
