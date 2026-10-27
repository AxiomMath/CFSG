module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Proof1422
public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofTransv

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

theorem item1420R_of (h1416 : Item1416R) (hL3 : Step1420NotL3R) (hA7 : Step1420NotA7R) :
    Item1420R := by
  intro G _ _ A c L hR hfail c' hc' L' hL'
  rcases (hR.toSec14Std.chosen136.2 c' hc'.1 L' hL').1 with hJ | hL | hA | hM22 | hM12
  · obtain ⟨φ⟩ := hJ
    exact ((h1416 G A c L hR hfail c' hc'.1 L' hL').false φ).elim
  · exact (hL3 G A c L hR hfail c' hc' L' hL' hL).elim
  · obtain ⟨φ⟩ := hA
    exact ((hA7 G A c L hR hfail c' hc' L' hL').false φ).elim
  · exact Or.inr hM22
  · exact Or.inl hM12

theorem step1422R_of_case3
    (h133 : Item133) (hNW : Step1422NotWHR)
    (hCe : Step1422CentR) (hSR : Step1422SR) (h146 : Item146S14) (hbot : Item145BotS14) :
    Step1422R :=
  step1422R_of (step1422TransvR_of h133 hNW) hCe hSR h146 hbot

end CFSG.RankThree.PartTwo.Sec14
