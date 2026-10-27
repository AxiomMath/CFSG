
module


public import Certificates.Kernel.MonsterB.Fischer3066

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Fischer.Cert in
theorem certificate3066 : (fShapeCheck = true)
    ∧ (fColCheck = true)
    ∧ (fFixCheck = true)
    ∧ (spanRankIs 78 (subOneRows (List.range 12)) 77 = true)
    ∧ (freeIs 78 (subOneRows (List.range 12)) [0] = true)
    ∧ (spanRankIs 78 ((List.range 22).map labelCoord) 11 = true)
    ∧ (coordNeCheck = true)
    ∧ (maskSum = 949) := KernelMonB.Fischer3066.facts

end Certificates
