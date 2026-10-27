module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSFiveData
import Certificates.Kernel.Misc.Perm.HS100.FiveGlue

public section

open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.HSFive

namespace Certificates

open CertificateChecks

theorem hsFiveOK_true : hsFiveOK = true := KernelMisc.HS100.Five.hsFiveOK_true

theorem certificate117031 : CFSG.EvenSporadicStandard.HSStd.Zassenhaus.HSFive.hsFiveOK = true := hsFiveOK_true

end Certificates
