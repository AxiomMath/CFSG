module

public import CFSG.RankThree.PartTwo.Sec17.J2CoverE8Inputs
import Certificates.Kernel.Misc.Perm.J2E8

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec17.J2CoverE8 in
theorem certificate724810 : chkJ2E8 = true := KernelMisc.J2Fam.chkJ2E8_K

end Certificates
