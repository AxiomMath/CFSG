module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Case1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem caseII_of_orth (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α β α' : Geo H M}
    (hc : IsCritData α β α') (hα : vtype α = true) (hz : ⁅Zv α, Zv α'⁆ = ⊥)
    (ho : IsOrthSec (stab β) (Vn β ⊓ Subgroup.centralizer (oTwoRes (stab β) : Set G)) (Vn β))
    (hb : 5 ≤ bMin H M) : CaseII H M := by
  have hS := Sit.of_orth hA h26 hc hα hz ho hb
  rcases C1.claim1 hS with h | hI
  · exact h
  · exact (caseI_false hS hI).elim

end S35

end F53.Stellmacher

end CFSG.Quasithin
