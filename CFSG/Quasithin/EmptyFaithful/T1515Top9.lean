module

public import CFSG.Quasithin.EmptyFaithful.T1515Top8
public import CFSG.Quasithin.EmptyFaithful.S151bSummary

public section

namespace CFSG.Quasithin

theorem theorem1515_of_inputs9
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hC65 : Construction1516SixFive)
    (h316 : Theorem316Statement) (h317 : Theorem317Statement) (h319 : Lemma319Statement)
    (h1414 : StageLemma1414) (h1416 : StageLemma1416) (h1417 : StageLemma1417)
    (hD : Description1512) (hN : Nilpotency1512) (hStep : Step1514Gen)
    (h17 : StageLemma1517) (h158 : StageLemma1518) (h1511one : StageLemma15111One)
    (h1512four : StageLemma15112Four)
    (hI19 : Lemma15119Input235) (hI20 : Lemma15120Input) (hI21 : Lemma15121Input)
    (hI22 : Lemma15122Input) (hI23 : Lemma15123Input) (hI24 : Lemma15124Input)
    (hI25 : Lemma15125InputRest) (hI27 : Lemma15127Input) (hI28 : Lemma15128Input)
    (hI29 : Lemma15129Input) : StageTheorem1515 := by
  obtain ⟨-, h15, -, h19, -, h113, h14⟩ :=
    stage151_of_inputs3 h316 h317 h319 h1414 h1416 h1417 hD hN hStep h17 h158 h1511one h1512four
  exact theorem1515_of_inputs8 h37 h38 h39 hC65 h15 h17 h19 (stageLemma15110_of h1416 h15) h113 h14
    hI19 hI20 hI21 hI22 hI23 hI24 hI25 hI27 hI28 hI29

end CFSG.Quasithin
