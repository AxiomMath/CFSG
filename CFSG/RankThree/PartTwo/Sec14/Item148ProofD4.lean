module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Sec13.Item136Pair

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS


theorem step148D4_of_data
    (hdata : Step148D4Data) : Step148D4 := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP hkt he J hJ hKJ hAJ h4
  obtain ⟨n, hn, hK, hJm, hind⟩ := h4
  obtain ⟨b, Jb, Lb, -, -, -, -, -, hbΩ, hLb, hJbLb, hbJb⟩ :=
    hdata G A c L h Y hY hs hYB B Q e K Le hP hkt he J hJ hKJ hAJ n hn ⟨hK, hJm, hind⟩
  have hD : Sec13Data G A b Lb :=
    { h.toSec13Data with zpowers_mem_omegaA := hbΩ, mem_lA := hLb }
  exact not_mem_of_center_eq_bot hD
    (Sec15.center_eq_bot_of_types hD.mem_thetaComponentsAt (h.chosen136.2 b hbΩ Lb hLb).1)
    (hJbLb hbJb)

end CFSG.RankThree.PartTwo.Sec14
