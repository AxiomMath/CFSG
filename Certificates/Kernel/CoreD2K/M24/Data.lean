module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.CoreD2Mathieu

namespace CertificateChecks.KernelCoreD2K.M24

open Certificates.CoreD2Perm

meta def gpM : Array (Array Nat) := gsT m24CoreData
meta def gpiM : Array (Array Nat) := giT m24CoreData
meta def gtM : Array (Array Nat) := gT m24CoreData
meta def gtiM : Array (Array Nat) := gTi m24CoreData
meta def egM : Array (Array Nat) := eGens m24CoreData

end CertificateChecks.KernelCoreD2K.M24

public section

#kmisc_packarrs CertificateChecks.KernelCoreD2K.M24.GP CertificateChecks.KernelCoreD2K.M24.gpM 5
#kmisc_packarrs CertificateChecks.KernelCoreD2K.M24.GPI CertificateChecks.KernelCoreD2K.M24.gpiM 5
#kmisc_packarrs CertificateChecks.KernelCoreD2K.M24.GT CertificateChecks.KernelCoreD2K.M24.gtM 5
#kmisc_packarrs CertificateChecks.KernelCoreD2K.M24.GTI CertificateChecks.KernelCoreD2K.M24.gtiM 5
#kmisc_packarrs CertificateChecks.KernelCoreD2K.M24.EG CertificateChecks.KernelCoreD2K.M24.egM 5

end
