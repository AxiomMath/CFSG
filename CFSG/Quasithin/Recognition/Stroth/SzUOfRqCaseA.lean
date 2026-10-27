module

public import CFSG.Quasithin.Recognition.Stroth.SzUOfGaps

import CFSG.Quasithin.Recognition.Stroth.Str83G5ConcWire
import CFSG.Quasithin.Recognition.Stroth.Str83TorusInjCaseB

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.H13

theorem str83SevenPath_of_rqEq_caseAFalse
    (hR : Str83RqEq) (hA : Str83G4CaseAFalse) : Str83SevenPath :=
  G5.str83SevenPath_of_orders (str83Orders_of_parts hR (str83Q1Order_of_caseAFalse hA))
    (str83TorusInj_of_caseAFalse hR hA)

theorem idSzL2W_of_rqEq_caseAFalse
    (hR : Str83RqEq) (hA : Str83G4CaseAFalse) : IdSzL2W :=
  idSzL2W_of_gaps hR hA (str83SevenPath_of_rqEq_caseAFalse hR hA)

theorem idSzL2_of_rqEq_caseAFalse
    (hR : Str83RqEq) (hA : Str83G4CaseAFalse) : IdSzL2 :=
  (idSzL2W_of_rqEq_caseAFalse hR hA).idSzL2

end CFSG.Quasithin.Stroth

end
