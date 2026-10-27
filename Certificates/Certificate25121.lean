module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataLocalFamNative
import Certificates.Kernel.J4Fam.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.J4Std.DataLocal in
theorem certificate25121 : chkFam = true := KernelJ4Fam.chkFam_true

end Certificates
