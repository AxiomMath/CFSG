module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OutData2
import Certificates.Kernel.Misc.Perm.HS100.OGlue

public section

open CFSG.EvenSporadicStandard.HSStd

namespace Certificates

open CertificateChecks

theorem s5fOK_true : s5fOK = true := KernelMisc.HS100.O.s5fOK_true

open CFSG.EvenSporadicStandard.HSStd in
theorem certificate26962 : s5fOK = true := s5fOK_true

end Certificates
