module

public import CFSG.RankThree.GF2n.Item310BridgesLie
public import CFSG.RankThree.GF2n.Item310BridgesSporadic

public section

namespace CFSG.RankThree.GF2n

theorem item310Bridges
    : Item310Bridges where
  omegaPlus := pOmegaPlusBridge
  omegaMinus := pOmegaMinusBridge
  g2 := chevalleyEvenBridge_G2
  trialityD4 := chevalleyEvenBridge_trialityD4
  twistedE6 := chevalleyEvenBridge_twistedE6
  e6 := chevalleyEvenBridge_E6
  e7 := chevalleyEvenBridge_E7
  e8 := chevalleyEvenBridge_E8
  suzuki := suzukiBridge
  m23 := sporadicBridge_M23
  m24 := sporadicBridge_M24
  j3 := sporadicBridge_J3
  j4 := sporadicBridge_J4
  co1 := sporadicBridge_Co1
  co2 := sporadicBridge_Co2
  hs := sporadicBridge_HS
  suz := sporadicBridge_Suz
  he := sporadicBridge_He
  fi24 := sporadicBridge_Fi24Prime
  hn := sporadicBridge_HN
  th := sporadicBridge_Th
  b := sporadicBridge_B
  m := sporadicBridge_M

theorem item3_10_of_gf2nTypeStatement
    (hGF2n : GF2nTypeStatement) : PartTwo.Sec6.Item3_10 :=
  item3_10_of_gf2nType hGF2n item310Bridges

end CFSG.RankThree.GF2n
