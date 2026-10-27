module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.CoreD2K.RuCent.Datum
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelCoreD2K.RuCent

open Certificates.CoreD2Perm

meta def gtM : Array (Array Nat) := gT ruCentK.base
meta def gtiM : Array (Array Nat) := gTi ruCentK.base
meta def egM : Array (Array Nat) := eGens ruCentK.base
meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 4060

end CertificateChecks.KernelCoreD2K.RuCent

public section

#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuCent.GT CertificateChecks.KernelCoreD2K.RuCent.gtM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuCent.GTI CertificateChecks.KernelCoreD2K.RuCent.gtiM 12

#kpenum CertificateChecks.KernelCoreD2K.RuCent.RE 4060 12 false
  CertificateChecks.KernelCoreD2K.RuCent.egM CertificateChecks.KernelCoreD2K.RuCent.egM
  CertificateChecks.KernelCoreD2K.RuCent.idT 125

end
