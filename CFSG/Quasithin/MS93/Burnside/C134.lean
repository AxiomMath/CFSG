module

public import CFSG.Quasithin.MS93.Burnside.Sp4HDesc
public import CFSG.Quasithin.MS93.S4LCoreDesc
public import CFSG.Quasithin.MS93.S4XKey

public section

namespace CFSG.Quasithin.MS93

theorem burnsideC134_s34FDescN (hsl : S4L.NoNonlinSLGt4) : S4L.Core.S34FDescN := by
  intro G _ _ M T L h hmin hb hc hb4 _ _ _ _
  rcases hc with ⟨hU, hF⟩ | ⟨hU, hF⟩
  · by_cases h4 : critDist (puAmalgam h.le) = 4
    · obtain ⟨hU', hF'⟩ := hb4 h4
      exact (S4L.burnsideSp4H_noNonlinSp G M T L h hmin hb hU'.isSp4U hF').elim
    · obtain ⟨m, hm⟩ := h.critDist_even
      have h4' : 4 < critDist (puAmalgam h.le) := by omega
      exact (hsl G M T L h hmin h4' hU.isSL3U hF).elim
  · exact (S4L.burnsideSp4H_noNonlinSp G M T L h hmin hb hU.isSp4U hF).elim

end CFSG.Quasithin.MS93
