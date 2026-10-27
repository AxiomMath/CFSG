module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SpecialData
import Certificates.Kernel.Misc.Perm.HS100.TGlue

public section

open CFSG.EvenSporadicStandard.HSStd.Zassenhaus

namespace Certificates

open CertificateChecks

theorem zasUniqOK_true : zasUniqOK = true := KernelMisc.HS100.T.zasUniqOK_true

open CFSG.EvenSporadicStandard.HSStd.Zassenhaus in
theorem certificate117003 : zasUniqOK = true := zasUniqOK_true

end Certificates
