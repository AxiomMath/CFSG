module

public import CFSG.RankThree.PartOne.K133Spor.HSPairInputs
import Certificates.Kernel.HS100.PairFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne.K133Spor in
theorem certificate14998 : HSPairFreeCheck := KernelHS100.hsPairFree

end Certificates
