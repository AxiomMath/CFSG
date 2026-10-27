module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.CoreD2RuThree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelCoreD2K.RuThree

open Certificates.CoreD2Perm

meta def gpM : Array (Array Nat) := gsT ruThreeLinesData.base
meta def gpiM : Array (Array Nat) := giT ruThreeLinesData.base
meta def gtM : Array (Array Nat) := gT ruThreeLinesData.base
meta def gtiM : Array (Array Nat) := gTi ruThreeLinesData.base
meta def egM : Array (Array Nat) := eGens ruThreeLinesData.base
meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 4060

end CertificateChecks.KernelCoreD2K.RuThree

public section

#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuThree.GP CertificateChecks.KernelCoreD2K.RuThree.gpM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuThree.GPI CertificateChecks.KernelCoreD2K.RuThree.gpiM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuThree.GT CertificateChecks.KernelCoreD2K.RuThree.gtM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuThree.GTI CertificateChecks.KernelCoreD2K.RuThree.gtiM 12

#kpenum CertificateChecks.KernelCoreD2K.RuThree.RE 4060 12 false
  CertificateChecks.KernelCoreD2K.RuThree.egM CertificateChecks.KernelCoreD2K.RuThree.egM
  CertificateChecks.KernelCoreD2K.RuThree.idT 27

end
