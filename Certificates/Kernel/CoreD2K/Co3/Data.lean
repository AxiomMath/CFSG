module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.CoreD2Co3

namespace CertificateChecks.KernelCoreD2K.Co3

open Certificates.CoreD2Perm

meta def gpM : Array (Array Nat) := gsT co3LinesData.base
meta def gpiM : Array (Array Nat) := giT co3LinesData.base
meta def gtM : Array (Array Nat) := gT co3LinesData.base
meta def gtiM : Array (Array Nat) := gTi co3LinesData.base
meta def egM : Array (Array Nat) := eGens co3LinesData.base
meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 276

end CertificateChecks.KernelCoreD2K.Co3

public section

#kmisc_packarrs CertificateChecks.KernelCoreD2K.Co3.GP CertificateChecks.KernelCoreD2K.Co3.gpM 9
#kmisc_packarrs CertificateChecks.KernelCoreD2K.Co3.GPI CertificateChecks.KernelCoreD2K.Co3.gpiM 9
#kmisc_packarrs CertificateChecks.KernelCoreD2K.Co3.GT CertificateChecks.KernelCoreD2K.Co3.gtM 9
#kmisc_packarrs CertificateChecks.KernelCoreD2K.Co3.GTI CertificateChecks.KernelCoreD2K.Co3.gtiM 9

#kpenum CertificateChecks.KernelCoreD2K.Co3.RE 276 9 false CertificateChecks.KernelCoreD2K.Co3.egM
  CertificateChecks.KernelCoreD2K.Co3.egM CertificateChecks.KernelCoreD2K.Co3.idT 125

end
