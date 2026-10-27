module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.S5A56FStmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5B

theorem s56_of_s56f (h56f : S5.S56f) : S56 := by
  intro G _ _ M T L h hmin hb k F _ _ a hd α' hc hαβ l hl hTl hJl
  obtain ⟨g, hg, x, hx, hconc⟩ := h56f G M T L h hmin hb k F _ _ a hd α' hc hαβ l hl hTl hJl
  exact ⟨g, hg, x, hx, hconc.1.1⟩

end S5B

end CFSG.Quasithin.MS93
