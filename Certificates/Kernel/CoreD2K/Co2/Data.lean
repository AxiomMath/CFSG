module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.CoreD2Co2
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelCoreD2K.Co2

open Certificates.CoreD2Perm

meta def gpM : Array (Array Nat) := gsT co2LinesData.base
meta def gpiM : Array (Array Nat) := giT co2LinesData.base
meta def gtM : Array (Array Nat) := gT co2LinesData.base
meta def gtiM : Array (Array Nat) := gTi co2LinesData.base
meta def egM : Array (Array Nat) := eGens co2LinesData.base
meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 2300

end CertificateChecks.KernelCoreD2K.Co2

public section

#kmisc_packarrs CertificateChecks.KernelCoreD2K.Co2.GP CertificateChecks.KernelCoreD2K.Co2.gpM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.Co2.GPI CertificateChecks.KernelCoreD2K.Co2.gpiM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.Co2.GT CertificateChecks.KernelCoreD2K.Co2.gtM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.Co2.GTI CertificateChecks.KernelCoreD2K.Co2.gtiM 12

#kpenum CertificateChecks.KernelCoreD2K.Co2.RE 2300 12 false CertificateChecks.KernelCoreD2K.Co2.egM
  CertificateChecks.KernelCoreD2K.Co2.egM CertificateChecks.KernelCoreD2K.Co2.idT 125

end
