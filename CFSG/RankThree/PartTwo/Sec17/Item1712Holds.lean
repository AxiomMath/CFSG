module

public import CFSG.RankThree.PartTwo.Sec17.Item177Holds
public import CFSG.RankThree.PartTwo.Sec17.Item1711Q
public import CFSG.RankThree.PartTwo.Sec17.Ronan1712Q8

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped Pointwise commutatorElement

theorem item1712S17_of_inputs
    (h310 : Sec6.Item3_10) (h135 : Item135)
    (h145 : Item145BotS14) (h146 : Item146S14) (h149 : Item149S14) (h1411 : Item1411_1S17)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (h166 : Item166S17) (h167 : Item167R)
    (h168 : Item168S17) (h172 : Item172S17) (h176 : Item176R) (h9 : CardInfNineS17)
    (h1444 : Item1444S14) : Item1712S17 := by
  obtain ⟨h45, h48, -, h422, -, -, -, -, h134, -, h142All⟩ := Ronan148M.closedInputs
  have h142 : Item142R := Sec14.item142R_of_wired h142All
  have h143c : Concl143S14 := Ronan148M.concl143S14_holds
  have h177 : Item177S17 := item177S17_of_inputs h310 h135 h145 h146 h149 h1411 h1514 hMeets
    h166 h167 h168 h172 h176 h9 h1444
  have h179 : Item179S17 := item179S17_of h166 (item145BotS17_of h145) h168 h146 h177
  have hKM : Step1711KM :=
    step1711KM_of_balance_meets_Q step143Balance_holds h48 h1514 hMeets h134
  have h1711 : Item1711S17 :=
    item1711S17_of_item166_concl143 h179 hKM h422 h45 h142 h143c h166
  have hsol17 : Sec17OThreeSolv :=
    sec17OThreeSolv_of_item174
      (item174_of_item143 h135 h145 h146 h149 h1411 h1514 hMeets h166 h167 h168 h172)
  have hsol : Step177OThreeSolv := step177OThreeSolv_of_sec17 hsol17
  have h171 : Item171S17 := item171S17_holds h1444 h146 h145 h1514 hMeets
  have hmeet : Step177Meet := step177Meet_holds h1444 h146 h145 h1514 hMeets
  have hcontra : Step177Contra := step177Contra_holds h171 h9 hsol
  have hmain : Step177MainB := step177MainB_holds h171 h9 hsol
  have hMB : Step177MainMB := step177MainMB_of_contra hcontra step143Balance_holds h9
  have hres : Step1712SevenY0 := step1712SevenY0_of_MB hMB h1514 h176 h9
  have hFaith : Step1712Faith := step1712Faith_of_items h310 h9
  have hQ8 : Step1712DeltaQ8 :=
    Ronan1712Q8.step1712DeltaQ8_of_faith hFaith Ronan148M.item143QS14_holds
  have hF : Step1712DeltaF :=
    step1712DeltaF_of_q8 hQ8 h1514 hMeets hFaith h176 step143Balance_holds hsol17
  have hD : Step1712Delta := step1712Delta_of_F hF h166 hKM
  exact item1712S17_of_B h1711 hmeet hmain h1514 h176 hres h310 h9 hD

theorem item1713S17_of_inputs
    (h310 : Sec6.Item3_10) (h135 : Item135)
    (h145 : Item145BotS14) (h146 : Item146S14) (h149 : Item149S14) (h1411 : Item1411_1S17)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (h166 : Item166S17) (h167 : Item167R)
    (h168 : Item168S17) (h172 : Item172S17) (h176 : Item176R) (h9 : CardInfNineS17)
    (h1444 : Item1444S14) : Item1713S17 :=
  item1713S17_of (item1712S17_of_inputs h310 h135 h145 h146 h149 h1411 h1514 hMeets h166 h167
    h168 h172 h176 h9 h1444) h172

theorem item1714S17_of_inputs
    (h310 : Sec6.Item3_10) (h135 : Item135)
    (h145 : Item145BotS14) (h146 : Item146S14) (h149 : Item149S14) (h1411 : Item1411_1S17)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (h166 : Item166S17) (h167 : Item167R)
    (h168 : Item168S17) (h172 : Item172S17) (h176 : Item176R) (h9 : CardInfNineS17)
    (h1444 : Item1444S14) (h165 : Item165S17) : Item1714S17 :=
  item1714S17_of (item1713S17_of_inputs h310 h135 h145 h146 h149 h1411 h1514 hMeets h166 h167
    h168 h172 h176 h9 h1444) h165

end CFSG.RankThree.PartTwo.Sec17
