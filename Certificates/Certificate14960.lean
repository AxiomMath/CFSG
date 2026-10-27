module

public import CFSG.RankThree.PartOne.SPOR.Co1PlanesData
import Certificates.Kernel.Co1Planes.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne.SPOR in
theorem certificate14960 : co1ClassOK co1PlaneA = true ∧ co1ClassOK co1PlaneC = true ∧
    co1ClassOK co1PlaneB = true := KernelCo1Planes.c14960

end Certificates
