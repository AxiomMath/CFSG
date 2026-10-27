module

public import CFSG.RankThree.PartOne.K133Spor.GBarInputs
import Certificates.Kernel.K133.GBarFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne.K133Spor in
theorem certificate14999 : GBarOK := KernelK133.gbarOK

end Certificates
