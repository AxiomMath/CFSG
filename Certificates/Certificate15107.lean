module

public import Certificates.Data.GMS78RuCzMatchCheck
import Certificates.Kernel.GMS78.W107

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GMS78 in
theorem certificate15107 : ((CFSG.CosetTable.genSub {r | r ∈ RuCz.p12Rels.map FreeGroup.mk}
        (CFSG.CosetTable.subsetOf RuCz.sub9.length [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
      (CFSG.CosetTable.genSub {r | r ∈ RuCz.p12Rels.map FreeGroup.mk}
        (CFSG.CosetTable.subsetOf RuCz.sub9.length [0, 1, 2, 3, 4, 5])).index ≤ 24) ∧
    RuCz.czmZ0Check = true ∧ RuCz.czmLetterCheck = true ∧
    RuCz.czmJCheck = true ∧ RuCz.czmRepCheck = true ∧ RuCz.czmInvolCheck = true := KernelGMS78.certificate107

end Certificates
