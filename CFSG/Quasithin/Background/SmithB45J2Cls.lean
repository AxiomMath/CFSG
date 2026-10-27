module

public import Certificates.Certificate260410
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.J2Cls

open CFSG.Sporadic.Schreier

theorem orderOf_mem_of_isPRegular (g : ↥j2P)
    (hg : IsPRegular 2 g) : orderOf g ∈ [1, 3, 5, 7, 15] :=
  Certificates.certificate260410.1 g hg

theorem card_pRegularClass_j2P :
    Fintype.card (PRegularClass 2 ↥j2P) ≤ 10 :=
  Certificates.certificate260410.2

end CFSG.Quasithin.J2Cls
