module

public import Certificates.Data.J2Fix280
import Certificates.Kernel.J2Fix280.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate111603 : CFSG.RankThree.PartTwo.J2Residue.C280.checkA () = true ∧
    CFSG.RankThree.PartTwo.J2Residue.C280.checkB () = true ∧
    CFSG.RankThree.PartTwo.J2Residue.C280.checkC () = true := KernelJ2Fix280.facts111603

end Certificates

end
