module

public import CFSG.RankThree.PartOne.KS.ONPwCheck
import Certificates.Kernel.Sporadic.ONPw.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne.ONPw in
theorem certificate14961 : Facts concreteEnv ∧ liftWords.length = nLifts := KernelSpor.ONPw.pw_facts

end Certificates
