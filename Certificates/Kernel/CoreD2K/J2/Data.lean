module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.CoreD2J2

namespace CertificateChecks.KernelCoreD2K.J2

open Certificates.CoreD2Perm

meta def gpM : Array (Array Nat) := gsT j2LinesData.base
meta def gpiM : Array (Array Nat) := giT j2LinesData.base
meta def gtM : Array (Array Nat) := gT j2LinesData.base
meta def gtiM : Array (Array Nat) := gTi j2LinesData.base
meta def egM : Array (Array Nat) := eGens j2LinesData.base
meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 315

end CertificateChecks.KernelCoreD2K.J2

public section

#kmisc_packarrs CertificateChecks.KernelCoreD2K.J2.GP CertificateChecks.KernelCoreD2K.J2.gpM 9
#kmisc_packarrs CertificateChecks.KernelCoreD2K.J2.GPI CertificateChecks.KernelCoreD2K.J2.gpiM 9
#kmisc_packarrs CertificateChecks.KernelCoreD2K.J2.GT CertificateChecks.KernelCoreD2K.J2.gtM 9
#kmisc_packarrs CertificateChecks.KernelCoreD2K.J2.GTI CertificateChecks.KernelCoreD2K.J2.gtiM 9

#kpenum CertificateChecks.KernelCoreD2K.J2.RE 315 9 false CertificateChecks.KernelCoreD2K.J2.egM
  CertificateChecks.KernelCoreD2K.J2.egM CertificateChecks.KernelCoreD2K.J2.idT 27

end
