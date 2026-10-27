module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.CoreD2Mathieu

namespace CertificateChecks.KernelCoreD2K.M12

open Certificates.CoreD2Perm

meta def gpM : Array (Array Nat) := gsT m12CoreData
meta def gpiM : Array (Array Nat) := giT m12CoreData
meta def gtM : Array (Array Nat) := gT m12CoreData
meta def gtiM : Array (Array Nat) := gTi m12CoreData
meta def egM : Array (Array Nat) := eGens m12CoreData

end CertificateChecks.KernelCoreD2K.M12

public section

#kmisc_packarrs CertificateChecks.KernelCoreD2K.M12.GP CertificateChecks.KernelCoreD2K.M12.gpM 4
#kmisc_packarrs CertificateChecks.KernelCoreD2K.M12.GPI CertificateChecks.KernelCoreD2K.M12.gpiM 4
#kmisc_packarrs CertificateChecks.KernelCoreD2K.M12.GT CertificateChecks.KernelCoreD2K.M12.gtM 4
#kmisc_packarrs CertificateChecks.KernelCoreD2K.M12.GTI CertificateChecks.KernelCoreD2K.M12.gtiM 4
#kmisc_packarrs CertificateChecks.KernelCoreD2K.M12.EG CertificateChecks.KernelCoreD2K.M12.egM 4

end
