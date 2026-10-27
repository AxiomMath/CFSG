module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcTitsTests
import Certificates.Kernel.LocalComp.Tits8Check

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15055 : CFSG.ComponentClassification.RankTwoExceptional.TitsSec8.titsSec8Check = true := KernelLC.Tits8.titsSec8Check_true

end Certificates
