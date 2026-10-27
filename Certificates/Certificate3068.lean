module

public import Certificates.Kernel.MonsterB.Fischer3068

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Fischer.Cert in
theorem certificate3068 : (fourCheck = true)
    ∧ (seedPre = 16058837531770935235962)
    ∧ (rootOpNum 949 16058837531770935235962 = 16058837527637121392057)
    ∧ (seedZeroCheck = true) := KernelMonB.Fischer3068.facts

end Certificates
