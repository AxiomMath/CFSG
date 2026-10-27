module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even19
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even20A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even20B
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenFinC

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem endgame (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M} (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ CosetGeom.nbrs α) (h : Hyp18 α β) : False :=
  final_contradiction hA h26 hs hb hβ h (out19 hA h26 hs hβ)
    (out20 hA h26 hs hb hβ h (out19 hA h26 hs hβ)
      (out20bc hA h26 hs hb hβ h (out19 hA h26 hs hβ)))

end CFSG.Quasithin.F53.Stellmacher.S43.Even
