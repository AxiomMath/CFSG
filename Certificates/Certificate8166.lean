module

public import CFSG.RankThree.PartTwo.KFacts.KS14MultJ2Inputs
import Certificates.Kernel.Misc.Perm.J2Mult5P

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.KFacts.KS14 CFSG.Blueprint CFSG.ComponentClassification.J2Cover
  CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
theorem certificate8166 : chkMult5 = true := KernelMisc.J2M5.facts_proved

end Certificates
