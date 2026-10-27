module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.I2ModelData
import Certificates.Kernel.Misc.Perm.HS100.NGlue

public section

open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2

namespace Certificates

open CertificateChecks

theorem i2ModelOK_true : i2ModelOK = true := KernelMisc.HS100.N.i2ModelOK_true

theorem certificate117021 : CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2.i2ModelOK = true := i2ModelOK_true

end Certificates
