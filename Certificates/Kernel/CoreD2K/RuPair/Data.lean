module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.CoreD2RuFive
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelCoreD2K.RuPair

open Certificates.CoreD2Perm

meta def gpM : Array (Array Nat) := gsT ruFiveCoreData
meta def gpiM : Array (Array Nat) := giT ruFiveCoreData
meta def gtM : Array (Array Nat) := gT ruFiveCoreData
meta def gtiM : Array (Array Nat) := gTi ruFiveCoreData
meta def egM : Array (Array Nat) := eGens ruFiveCoreData

end CertificateChecks.KernelCoreD2K.RuPair

public section

#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuPair.GP CertificateChecks.KernelCoreD2K.RuPair.gpM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuPair.GPI CertificateChecks.KernelCoreD2K.RuPair.gpiM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuPair.GT CertificateChecks.KernelCoreD2K.RuPair.gtM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuPair.GTI CertificateChecks.KernelCoreD2K.RuPair.gtiM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuPair.EG CertificateChecks.KernelCoreD2K.RuPair.egM 12

end
