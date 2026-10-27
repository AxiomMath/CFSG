module

public import CFSG.RankThree.PartOne.S11.CatalogLeaves
public import CFSG.RankThree.PartOne.S11c.LyPlaneCore
public import CFSG.RankThree.PartOne.S11c.Sec66TFamily

public section

namespace CFSG.RankThree.PartOne

theorem lyLargePrimePlaneCentralization :
    LyLargePrimePlaneCentralization := by
  intro T _ _ hsimple hnab hLy p E U hpl
  have hp : p.Prime := hpl.prime
  have hp3 : 3 < p := hpl.three_lt
  have := hpl.elementary
  have hp5 : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    rw [h4] at hp
    norm_num at hp
  have hcenter : Subgroup.center T = ⊥ := Sec66T.center_eq_bot_of_simple' hnab
  exact ly_plane_core hLy hcenter hp hp5 E hpl.card U hpl.two_group hpl.normalized

end CFSG.RankThree.PartOne
