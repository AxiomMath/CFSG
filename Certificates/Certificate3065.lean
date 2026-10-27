
module


public import Certificates.Kernel.MonsterB.Fischer3065

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Fischer.Cert in
theorem certificate3065 : (gramWordCheck = true)
    ∧ (gramInvCheck = true)
    ∧ (coordCheck = true)
    ∧ ((List.range 78).map basisPt =
       [0, 1, 2, 3, 4, 6, 7, 8, 10, 12, 14, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 38,
         39, 40, 42, 54, 55, 56, 57, 58, 59, 60, 62, 63, 64, 66, 70, 71, 72, 74, 86, 87, 88, 90,
         94, 102, 118, 150, 151, 152, 154, 158, 166, 182, 278, 279, 282, 286, 294, 310, 406, 534,
         535, 538, 566, 1046, 1047, 1078, 1110, 1174, 1270, 1334, 1462, 1686, 1942, 2326]) := KernelMonB.F3065.facts

end Certificates
