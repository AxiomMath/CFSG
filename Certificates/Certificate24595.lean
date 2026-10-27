module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J3Table
import Certificates.Kernel.Sporadic.OddCore.J3TabF

public section

namespace Certificates

open CertificateChecks

theorem certificate24595 : CFSG.EvenSporadicStandard.Fin76b.J3.j3E_check = true := KernelSpor.J3Tab.facts24595

end Certificates
