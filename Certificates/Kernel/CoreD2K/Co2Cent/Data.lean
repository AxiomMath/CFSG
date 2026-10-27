module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.CoreD2K.Co2Cent.Datum
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelCoreD2K.Co2Cent

open Certificates.CoreD2Perm

meta def gtM : Array (Array Nat) := gT co2CentK.base
meta def gtiM : Array (Array Nat) := gTi co2CentK.base

end CertificateChecks.KernelCoreD2K.Co2Cent

public section

#kmisc_packarrs CertificateChecks.KernelCoreD2K.Co2Cent.GT CertificateChecks.KernelCoreD2K.Co2Cent.gtM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.Co2Cent.GTI CertificateChecks.KernelCoreD2K.Co2Cent.gtiM 12

end
