module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
import Certificates.Kernel.Misc.RuThreeM10.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.RuStd.S2 CFSG.RankThree.PartOne CFSG.RankThree.Native
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier in
theorem certificate24948 :
    CFSG.RankThree.Native.enumOK 11 ruThreeM11 ruThreeKeys11 ruThreeM11Cert = true ∧
      CFSG.RankThree.Native.enumOK 11 ruThreeM ruThreeKeys11 ruThreeTCert = true ∧
      ruThreeStabOK = true ∧ ruThreeStabCoverOK = true ∧ ruThreeCenterOK = true ∧
      oddNormalOK 11 ruThreeTCert = true := KernelMisc.RuThreeM10.m10_ok

end Certificates
