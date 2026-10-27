module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointInputs

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.CosetTable

@[expose] def farRels : List (List (Fin 18 × Bool)) :=
  [[(10, true), (16, true), (10, false), (16, false)],
    [(10, true), (17, true), (10, false), (17, false)],
    [(11, true), (16, true), (11, false), (16, false)],
    [(11, true), (17, true), (11, false), (17, false)]]

@[expose] def relsP6 (_ : Unit := ()) : List (List (Fin 18 × Bool)) :=
  relsP ++ farRels

@[expose] def checkIndex2016 (_ : Unit := ()) : Bool :=
  subsetCheckShortCC (relsP6 ()) chart5 13 2000000 2016

end CFSG.StandardType.QTwo.SixPoint

end
