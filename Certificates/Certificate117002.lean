module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SpecialData
import Certificates.Kernel.Misc.Perm.HS100.SpGlue

public section

namespace Certificates

open CFSG.EvenSporadicStandard.HSStd.Zassenhaus in
theorem certificate117002 : zasSpecialOK = true :=
  CertificateChecks.KernelMisc.HS100.Sp.zasSpecialOK_true

end Certificates
