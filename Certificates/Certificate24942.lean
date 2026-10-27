module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuTwoBInputs
import Certificates.Kernel.RuTwoB.Final

public section

namespace Certificates

theorem certificate24942 : CFSG.EvenSporadicStandard.RuStd.S2.ruTwoBCheck = true :=
  CertificateChecks.KernelRuTwoB.ruTwoB_check

end Certificates
