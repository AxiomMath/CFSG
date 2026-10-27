module

public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
public import CFSG.Timmesfeld.Transvection.PointsDetermined

public section

namespace CFSG.RankThree.GF2n.Tim81

theorem tim90Points : Tim90Points := by
  intro H _ _ Δ hΔ _ hN
  exact hΔ.pointsDetermined_of_forall_nilpotent hN

end CFSG.RankThree.GF2n.Tim81
