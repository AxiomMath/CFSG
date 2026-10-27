module

public import CFSG.RankThree.GF2n.Stroth80.Sec8EndMain
public import CFSG.RankThree.GF2n.Stroth80.Sec8CentreModel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem Vt_le_Sec8V1 {G : Type} [Group G] (M Q Z B : Subgroup G) (t r : G) :
    Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r :=
  le_inf le_sup_right le_sup_right

theorem step85Sylow_of_first (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hzt : Sec8ZtStatement) (h310chi : Stroth310ChiStatement)
    (hFirst : Step85FirstStatement) : Step85SylowStatement := by
  intro G _ _ M Q Z B hc n t hs _ Z0 hZ0 x hx _ ⟨z, hz, hzq⟩
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hconc := hFirst G M Q Z B hc n t hs r hr Z0 hZ0 x hx
  have hxK : x ∈ NormH0 M Z Z0 := by
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z := fun v hv =>
    hconc.2.1 v (Vt_le_Sec8V1 M Q Z B t r hv)
  exact hzq (commZ0_mem_Q_of_centralizes_Vt hc hZ0
    (fun z hz w hw => sec8_W_centralized h51 hA hzt h310chi hc hs hZ0 hz hw)
    (fun u hu huQ => sec8_ZV_of_parts h51 hA hzt h310chi hc hs hZ0 hu huQ) hxK.1 hxV z hz)

end CFSG.RankThree.GF2n.Stroth80
