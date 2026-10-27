module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctBasic
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctAct
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctRank
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctInt

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.GH74.GLS.SP CFSG.LieType.Ree.ReeTag

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem octRGD2 (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a) :=
  octRGD2_of_fields octComm octNilp (octConj₁ hK) (octConj₂ hK) octSq₁ octSq₂ octPow octUH
    octNeBot (octInv hK) octCarrier octUnique octRev octSub octAct₁ octAct₂ octMeet octRank₁
    octRank₂

end CFSG.Quasithin.H13.F431.TwoF4
