module

public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofDefs
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

section Item1416

theorem item1416R_of (h142 : Concl142S14) (h146 : Item146S14) (hbot : Item145BotS14) :
    Item1416R := by
  intro G _ _ A c L hR hfail c' hc' L' hL'
  refine ⟨fun φ => ?_⟩
  have hS := hR.toSec14Std
  have h' : Sec14Std G A c' L' := Proof1413.sec14Std_at hS hc' hL'
  obtain ⟨U₁, hU₁, U₂, hU₂, hne, hmeet, hXU⟩ :=
    exists_scriptQPiStar_two_of_j2 h' (fun Q hQ => h142 G A c L hS c' hc' Q hQ) ⟨φ⟩
  exact rank3II_14_16_false_std h' (h146 G A c' L' h') (hbot G A c' L' h') hfail.2 hU₁ hU₂ hne
    hmeet hXU

end Item1416

end CFSG.RankThree.PartTwo.Sec14
