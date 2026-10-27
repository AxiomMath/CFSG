module

public import CFSG.RankThree.PartOne.KS.NoPlane
public import CFSG.RankThree.PartOne.KS.J2
public import CFSG.RankThree.PartOne.KS.Suz
public import CFSG.RankThree.PartOne.KS.Co3

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint.NativeSporadic (Carrier)

structure SporadicOpenInputs : Prop where
  fi22 : SectionsForceEvenRankFour (Carrier .Fi22)
  fi23 : SectionsForceEvenRankFour (Carrier .Fi23)
  fi24 : SectionsForceEvenRankFour (Carrier .Fi24Prime)
  b : SectionsForceEvenRankFour (Carrier .B)
  m : SimplePresentationMSectionsForceEvenRankFour
  j4 : SporadicPlaneOdd (Carrier .J4)
  co1 : SporadicPlaneOdd (Carrier .Co1)
  co2 : SporadicPlaneOdd (Carrier .Co2)
  co3 : Co3AllInner
  hs : SporadicPlaneOdd (Carrier .HS)
  mcl : SporadicPlaneOdd (Carrier .McL)
  he : SporadicPlaneOdd (Carrier .He)
  ru : SporadicPlaneOdd (Carrier .Ru)
  on : SporadicPlaneOdd (Carrier .ONan)
  hn : SporadicPlaneOdd (Carrier .HN)
  ly : SporadicPlaneOdd (Carrier .Ly)
  th : SporadicPlaneOdd (Carrier .Th)

theorem original_sporadic_component_local_core_odd_action_of_inputs (h : SporadicOpenInputs) :
    OriginalSporadicComponentLocalCoreOddAction :=
  original_sporadic_component_local_core_odd_action_of_cases
    ⟨h.fi22, h.fi23, h.fi24, h.b, h.m⟩
    ⟨sporadicPlaneOdd_M11, sporadicPlaneOdd_M12, sporadicPlaneOdd_M22, sporadicPlaneOdd_M23,
      sporadicPlaneOdd_M24, sporadicPlaneOdd_J1, sporadicPlaneOdd_J2, sporadicPlaneOdd_J3, h.j4,
      h.co1, h.co2, sporadicPlaneOdd_Co3 h.co3, h.hs, h.mcl, h.he, h.ru, sporadicPlaneOdd_Suz,
      h.on, h.hn, h.ly, h.th⟩

end CFSG.RankThree.PartOne
