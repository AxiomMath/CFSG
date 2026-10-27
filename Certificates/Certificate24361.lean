module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.WordsInputs
import Certificates.Kernel.Misc.RuFourth.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate24361 : CFSG.EvenSporadicStandard.TwoRu.ruFourthCheck = true :=
  CFSG.KC.Misc.RuFourth.fourthK_sound KernelMisc.RuFourth.rho_eq KernelMisc.RuFourth.p0_eq
    KernelMisc.RuFourth.permOKs KernelMisc.RuFourth.lettersOK KernelMisc.RuFourth.zMoves
    KernelMisc.RuFourth.w1OK KernelMisc.RuFourth.w2OK

end Certificates

end
