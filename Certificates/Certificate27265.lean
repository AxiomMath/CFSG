module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSCliqueData
import Certificates.Kernel.Misc.Perm.HS100.CliqueGlue

public section

open CFSG.EvenSporadicStandard.HSStd.PumpHS

namespace Certificates

open CertificateChecks

theorem cliqueOK_true : cliqueOK = true := KernelMisc.HS100.Clique.cliqueOK_true

theorem certificate27265 : CFSG.EvenSporadicStandard.HSStd.PumpHS.cliqueOK = true := cliqueOK_true

end Certificates
