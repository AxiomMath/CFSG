module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42GtMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.CardZvTwoSec
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Frontier2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem hss42CardGtAt_of_hss28 (hA : F53Amalgam H M S) (h28 : Hss28At H M) :
    Hss42CardGtAt H M := fun α β α' hc hα _ hz hb => by
  have hzβ := Zv_central_of_comm_eq_bot hA hc hz
  exact EmptyFaithful.Stellmacher.OrdinaryProofs.card_Zv_eq_two_of_sec hA hα hc.adj hzβ
    (hss42Comm_gt hA h28 hc hα hz hb)

end F53.Stellmacher

end CFSG.Quasithin
