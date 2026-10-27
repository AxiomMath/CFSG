module

public import CFSG.Quasithin.EmptyFaithful.SzN25G2

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace SzN25

section Top


theorem input49K_holds (h113 : StageLemma14113) (h56 : AsB56) (hG2 : FactG2Cayley) :
    S1549C.Input49K :=
  SzN22.input49K_of_lieRigid h113 h56
    (SzN23.lieRigid_of_rankTwo (SzN24.lieRigidRankTwo_of_g2 (lieRigidG2_holds hG2)))

end Top

end SzN25

end CFSG.Quasithin
