module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
import Certificates.Kernel.RuThree.GraphFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.RuStd.S2 CFSG.RankThree.PartOne CFSG.RankThree.Native
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier in
theorem certificate24947 :
    CFSG.EvenSporadicStandard.RuStd.S2.prodOK 4060 11 ruThreeC0Gens ruThreeM ruThreeKeys ruThreeGraphCert = true ∧
      ruThreeGraphCert.pts.size = 2160 ∧ ruThreeKernelOK = true ∧
      eqA 11 ruThreeM[0]! (CFSG.Monster.B.Co2.Native.idA 11) = true := KernelRuThree.ok24947

end Certificates
