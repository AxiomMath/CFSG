module

public import CFSG.Sporadic.SmallOddCore.J3CentFacts
import Certificates.Kernel.SporSch.PairJ3.C81Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate2281 : CFSG.Sporadic.SmallOddCore.j3CentFacts := KernelSporSch.PJ3C81.facts

end Certificates
