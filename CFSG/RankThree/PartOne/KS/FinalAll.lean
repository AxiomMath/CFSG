module

public import CFSG.RankThree.PartOne.KS.Final
public import CFSG.RankThree.PartOne.KS.PlaneJ4
public import CFSG.RankThree.PartOne.KS.PlaneTh
public import CFSG.RankThree.PartOne.KP.BExclusion
public import CFSG.RankThree.PartOne.KP.MSectionMonster
public import CFSG.RankThree.PartOne.SPOR.Final

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint.NativeSporadic (Carrier)

structure SporadicPlaneInputs : Prop where
  co1 : SporadicPlaneOdd (Carrier .Co1)
  hn : SporadicPlaneOdd (Carrier .HN)
  ly : SporadicPlaneOdd (Carrier .Ly)

theorem original_sporadic_component_local_core_odd_action_of_plane_inputs_and_on
    (h : SporadicPlaneInputs) (hon : ONPointwiseSeven) : OriginalSporadicComponentLocalCoreOddAction :=
  original_sporadic_component_local_core_odd_action_of_final_inputs
    { b := sectionsForceEvenRankFour_B
      mSection := simplePresentationMHasBSection_holds
      j4 := sporadicPlaneOdd_J4
      co1 := h.co1
      co2 := SPOR.co2AllInner_holds
      on := hon
      hn := h.hn
      ly := h.ly
      th := sporadicPlaneOdd_Th }

end CFSG.RankThree.PartOne
