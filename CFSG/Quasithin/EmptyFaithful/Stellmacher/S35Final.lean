module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Case2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Assembly2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem caseII_false (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α β α' : Geo H M}
    (hc : IsCritData α β α') (hα : vtype α = true) (hz : ⁅Zv α, Zv α'⁆ = ⊥)
    (ho : IsOrthSec (stab β) (Vn β ⊓ Subgroup.centralizer (oTwoRes (stab β) : Set G)) (Vn β))
    (hb : 5 ≤ bMin H M) (hII : CaseII H M) : False :=
  caseII_false_of_sit (Sit.of_orth hA h26 hc hα hz ho hb) hII

theorem hss35OrthAt_of (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) : Hss35OrthAt H M := by
  intro α β α' hc hα hz ho
  by_contra hgt
  have h3 : 3 < bMin H M := Nat.lt_of_not_ge hgt
  have hG := S34.Glob.of_crit hA (hss28At_of_hss26A hA h26) hc hα hz
  obtain ⟨k, hk⟩ := hG.odd
  have hb : 5 ≤ bMin H M := by omega
  exact caseII_false hA h26 hc hα hz ho hb (caseII_of_orth hA h26 hc hα hz ho hb)

end S35

end F53.Stellmacher

end CFSG.Quasithin
