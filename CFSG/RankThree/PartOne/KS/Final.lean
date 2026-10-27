module

public import CFSG.RankThree.PartOne.KS.Main
public import CFSG.RankThree.PartOne.KS.FischerSections
public import CFSG.RankThree.PartOne.KS.HSMcL
public import CFSG.RankThree.PartOne.KS.Ru
public import CFSG.RankThree.PartOne.KS.Co2
public import CFSG.RankThree.PartOne.KS.He
public import CFSG.RankThree.PartOne.KS.ONPlane
public import CFSG.RankThree.PartOne.KP.Fi22Section
public import CFSG.RankThree.PartOne.KP.Co3Aut

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint.NativeSporadic (Carrier)

structure SporadicFinalInputs : Prop where
  b : SectionsForceEvenRankFour (Carrier .B)
  mSection : SimplePresentationMHasBSection
  j4 : SporadicPlaneOdd (Carrier .J4)
  co1 : SporadicPlaneOdd (Carrier .Co1)
  co2 : Co2AllInner
  on : ONPointwiseSeven
  hn : SporadicPlaneOdd (Carrier .HN)
  ly : SporadicPlaneOdd (Carrier .Ly)
  th : SporadicPlaneOdd (Carrier .Th)

theorem original_sporadic_component_local_core_odd_action_of_final_inputs
    (h : SporadicFinalInputs) : OriginalSporadicComponentLocalCoreOddAction := by
  obtain ⟨h23, h24⟩ := sectionsForceEvenRankFour_fi23_fi24prime sectionsForceEvenRankFour_Fi22
    hasSection_fi23_fi22 hasSection_fi24prime_fi23
  exact original_sporadic_component_local_core_odd_action_of_inputs
    { fi22 := sectionsForceEvenRankFour_Fi22
      fi23 := h23
      fi24 := h24
      b := h.b
      m := simplePresentationM_sections_of_B_section h.b h.mSection
      j4 := h.j4
      co1 := h.co1
      co2 := sporadicPlaneOdd_Co2 h.co2
      co3 := co3P_allInner
      hs := sporadicPlaneOdd_HS
      mcl := sporadicPlaneOdd_McL
      he := sporadicPlaneOdd_He
      ru := sporadicPlaneOdd_Ru
      on := sporadicPlaneOdd_ONan h.on
      hn := h.hn
      ly := h.ly
      th := h.th }

end CFSG.RankThree.PartOne
