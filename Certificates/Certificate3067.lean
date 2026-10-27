module

public import Certificates.Kernel.MonsterB.Fischer3067

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Fischer.Cert in
theorem certificate3067 : (tableCheck = true)
    ∧ (radicalCheck = true)
    ∧ (spanRankIs 78 (subOneRows transIdx) 67 = true)
    ∧ (freeIs 78 (subOneRows transIdx) (List.range 11) = true)
    ∧ (orbitCheck = true)
    ∧ (∀ t < 8,
       ((Finset.range 2048).filter fun m => orbIdx m = t).card = orbLen t)
    ∧ (zeroSetCheck = true) := KernelMonB.F3067.facts

end Certificates
