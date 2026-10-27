module

public import CFSG.Quasithin.EmptyFaithful.S1516
public import CFSG.Quasithin.EmptyFaithful.S15112
public import CFSG.Quasithin.EmptyFaithful.S15113
public import CFSG.Quasithin.EmptyFaithful.S15114

public section

namespace CFSG.Quasithin

theorem stage151_of_inputs (h316 : Theorem316Statement) (h317 : Theorem317Statement)
    (h319 : Lemma319Statement) (h1414 : StageLemma1414) (h1416 : StageLemma1416)
    (h1417 : StageLemma1417) (hD : Description1512) (hN : Nilpotency1512) (hStep : Step1514Gen)
    (h157 : StageLemma1517) (h158 : StageLemma1518) (h1511 : StageLemma15111)
    (h1512four : StageLemma15112Four) (h3 : StageLemma15113Three) (h4 : StageLemma15113Four) :
    StageLemma1511 ∧ StageLemma1515 ∧ StageLemma1516 ∧ StageLemma1519 ∧ StageLemma15112 ∧
      StageLemma15113 ∧ StageLemma15114 := by
  have h15 : StageLemma1515 := stageLemma1515_of_description hD
  have h16 : StageLemma1516 := stageLemma1516_of hN
  have h159 : StageLemma1519 := stageLemma1519_of h1414 h1417 h317 h15 h16
  have h1512 : StageLemma15112 :=
    stageLemma15112_of h319 h1416 h15 h158 h159 h16 h1511 h1512four
  exact ⟨stageLemma1511_of_theorem316 h316, h15, h16, h159, h1512,
    stageLemma15113_of h157 h159 h1512 h3 h4, stageLemma15114_of hStep h157 h15 h159 h16 h1512⟩

end CFSG.Quasithin
