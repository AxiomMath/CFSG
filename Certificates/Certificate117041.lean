module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0Data
import Certificates.Kernel.Misc.Perm.HS100.S0Glue

public section

open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0

namespace Certificates

open CertificateChecks

theorem s0OK_true : s0OK = true := KernelMisc.HS100.S0.s0OK_true

theorem certificate117041 : CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.s0OK = true := s0OK_true

end Certificates
