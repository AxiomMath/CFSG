module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.TransDataWords
import CFSG.Certificates.Kernel.SxtSound
import Certificates.Kernel.LocalQT.Syl.C4137
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CertificateChecks.Batch24841

open CFSG.KC.Ord CFSG.KC.Sxt CFSG.KD.LQT.C4137 CFSG.QuasithinUnique.Setup.X1
  CFSG.EvenSporadicStandard.M24Std

private theorem ch24841 : sxtK GC m24RGens m24E1Bw [wordSxtN1, wordSxtN2] wordSxtR
    [wordSxtQ1, wordSxtQ2, wordSxtQ3] wordsSxtQ sxtW1 sxtW2 = true := by quickRfl

private theorem ch24841n : notB (sxtK GC m24RGens m24E1Bw [wordSxtN1, wordSxtN2] wordSxtR
    [wordSxtQ1, wordSxtQ2, wordSxtQ3] wordsSxtQ sxtW1 sxtW1) = true := by quickRfl

private theorem sxtData_0 : CFSG.EvenSporadicStandard.M24Std.SxtData :=
  sxtData_of hG ch24841

end CertificateChecks.Batch24841

namespace Certificates

open CertificateChecks

theorem certificate24841 : CFSG.EvenSporadicStandard.M24Std.SxtData := by
  exact CertificateChecks.Batch24841.sxtData_0

end Certificates
