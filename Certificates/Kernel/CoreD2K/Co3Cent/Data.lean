module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.CoreD2K.Co3Cent.Datum

namespace CertificateChecks.KernelCoreD2K.Co3Cent

open Certificates.CoreD2Perm

meta def gtM : Array (Array Nat) := gT co3CentK.base
meta def gtiM : Array (Array Nat) := gTi co3CentK.base

end CertificateChecks.KernelCoreD2K.Co3Cent

public section

#kmisc_packarrs CertificateChecks.KernelCoreD2K.Co3Cent.GT CertificateChecks.KernelCoreD2K.Co3Cent.gtM 9
#kmisc_packarrs CertificateChecks.KernelCoreD2K.Co3Cent.GTI CertificateChecks.KernelCoreD2K.Co3Cent.gtiM 9

end
