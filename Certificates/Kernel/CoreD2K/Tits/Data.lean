module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.CoreD2Tits
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelCoreD2K.Tits

open Certificates.CoreD2Perm

meta def gpM : Array (Array Nat) := gsT titsData
meta def gpiM : Array (Array Nat) := giT titsData
meta def gtM : Array (Array Nat) := gT titsData
meta def gtiM : Array (Array Nat) := gTi titsData
meta def egM : Array (Array Nat) := eGens titsData

end CertificateChecks.KernelCoreD2K.Tits

public section

#kmisc_packarrs CertificateChecks.KernelCoreD2K.Tits.GP CertificateChecks.KernelCoreD2K.Tits.gpM 11
#kmisc_packarrs CertificateChecks.KernelCoreD2K.Tits.GPI CertificateChecks.KernelCoreD2K.Tits.gpiM 11
#kmisc_packarrs CertificateChecks.KernelCoreD2K.Tits.GT CertificateChecks.KernelCoreD2K.Tits.gtM 11
#kmisc_packarrs CertificateChecks.KernelCoreD2K.Tits.GTI CertificateChecks.KernelCoreD2K.Tits.gtiM 11
#kmisc_packarrs CertificateChecks.KernelCoreD2K.Tits.EG CertificateChecks.KernelCoreD2K.Tits.egM 11

end
