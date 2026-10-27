module

public import CFSG.Quasithin.Background.Harris.R1.J2VertCheck
import Certificates.Kernel.J2Vert.Split300203Facts
public import CFSG.Quasithin.Background.Harris.R1.J2VertTables

public section

namespace Certificates

open CFSG.Quasithin.Background.Harris.R1.J2Vert CFSG.Monster.B.Co2.Native in
theorem certificate300203 :
    (relCheck 64 sArrs (vRels false) = true)
    ∧ (tabLower 64 sArrs tabS 3840 = true)
    ∧ (tabMem 64 sArrs tabS tsArrs 3 = true)
    ∧ (tabLower 64 tsArrs tabTs 256 = true)
    ∧ (tabClosed 64 tsArrs 3 tabTs = true)
    ∧ (tabClosed 64 (sArrs.extract 0 5) 5 tabQs = true)
    ∧ (normalLineCheck 64 sArrs tsArrs 3 (buildTab 64 (sArrs.extract 0 5) tabQs) = true)
    ∧ (centCount 64 (buildTab 64 tsArrs tabTs) (sArrs.getD 1 (idA 64)) = 128)
    ∧ (rootCount 64 (buildTab 64 tsArrs tabTs) (sArrs.getD 1 (idA 64)) (sArrs.getD 0 (idA 64))
        = 28)
    ∧ (rootCount 64 (buildTab 64 tsArrs tabTs) (sArrs.getD 1 (idA 64)) (sArrs.getD 1 (idA 64))
        = 12)
    ∧ (rootCount 64 (buildTab 64 tsArrs tabTs) (sArrs.getD 1 (idA 64))
        (compA 64 (sArrs.getD 0 (idA 64)) (sArrs.getD 1 (idA 64))) = 12) :=
  CertificateChecks.KernelJ2Vert.Split.facts

end Certificates
