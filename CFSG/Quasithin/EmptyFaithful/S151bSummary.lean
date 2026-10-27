module

public import CFSG.Quasithin.EmptyFaithful.S151Summary
public import CFSG.Quasithin.EmptyFaithful.S151b110
public import CFSG.Quasithin.EmptyFaithful.S151b111

public section

namespace CFSG.Quasithin

theorem stage151_of_inputs2 (h316 : Theorem316Statement) (h317 : Theorem317Statement)
    (h319 : Lemma319Statement) (h1414 : StageLemma1414) (h1416 : StageLemma1416)
    (h1417 : StageLemma1417) (hD : Description1512) (hN : Nilpotency1512) (hStep : Step1514Gen)
    (h157 : StageLemma1517) (h158 : StageLemma1518) (h1511 : StageLemma15111)
    (h1512four : StageLemma15112Four) :
    StageLemma1511 ∧ StageLemma1515 ∧ StageLemma1516 ∧ StageLemma1519 ∧ StageLemma15112 ∧
      StageLemma15113 ∧ StageLemma15114 := by
  have h15 : StageLemma1515 := stageLemma1515_of_description hD
  have h16 : StageLemma1516 := stageLemma1516_of hN
  have h159 : StageLemma1519 := stageLemma1519_of h1414 h1417 h317 h15 h16
  have h15110 : StageLemma15110 := stageLemma15110_of h1416 h15
  exact stage151_of_inputs h316 h317 h319 h1414 h1416 h1417 hD hN hStep h157 h158 h1511 h1512four
    (stageLemma15113Three_of h157 h158 h159 h15 h15110)
    (stageLemma15113Four_of h157 h158 h159 h15 h15110 h1512four)

theorem stage151_of_inputs3 (h316 : Theorem316Statement) (h317 : Theorem317Statement)
    (h319 : Lemma319Statement) (h1414 : StageLemma1414) (h1416 : StageLemma1416)
    (h1417 : StageLemma1417) (hD : Description1512) (hN : Nilpotency1512) (hStep : Step1514Gen)
    (h157 : StageLemma1517) (h158 : StageLemma1518) (h1511one : StageLemma15111One)
    (h1512four : StageLemma15112Four) :
    StageLemma1511 ∧ StageLemma1515 ∧ StageLemma1516 ∧ StageLemma1519 ∧ StageLemma15112 ∧
      StageLemma15113 ∧ StageLemma15114 := by
  have h15 : StageLemma1515 := stageLemma1515_of_description hD
  have h16 : StageLemma1516 := stageLemma1516_of hN
  have h159 : StageLemma1519 := stageLemma1519_of h1414 h1417 h317 h15 h16
  exact stage151_of_inputs2 h316 h317 h319 h1414 h1416 h1417 hD hN hStep h157 h158
    (stageLemma15111_of_one h158 h159 h1511one) h1512four

end CFSG.Quasithin
