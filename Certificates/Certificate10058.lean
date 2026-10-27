module

public import CFSG.RankThree.PartOne.S11c.J4RankInputs
import Certificates.Kernel.J4F2.Minor

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne CFSG.Sporadic.J4Schreier in
theorem certificate10058 :
    (MinorCheck (etaP 1).1 minorQ1 minorB1)
    ∧ (MinorCheck (etaP 14).1 minorQ14 minorB14) := KernelJ4F2.c10058

end Certificates
