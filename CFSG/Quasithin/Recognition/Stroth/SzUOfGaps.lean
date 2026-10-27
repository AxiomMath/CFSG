module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Holds
public import CFSG.Quasithin.Recognition.Stroth.Str83PathFixWindow
public import CFSG.Quasithin.Recognition.Stroth.Str86ShapeAssembly
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseB

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.H13

theorem idSzL2W_of_gaps
    (hR : Str83RqEq) (hA : Str83G4CaseAFalse) (hSP : Str83SevenPath) : IdSzL2W := by
  have hI : Str83CaseI := str83CaseI_of_rqEq hR
  have hO83 : Str83Orders := str83Orders_of_parts hR (str83Q1Order_of_caseAFalse hA)
  exact idSzL2W_of_leaves (str83LocTrans9_of_pathFix hO83 (str83PathFix_of_sevenPath hO83 hSP))
    hO83
    (str83Kernel_of_borelInf (str83BorelInf_of_caseI hI (str83TorusFaithful_of_caseI hR hI)))
    weiss80Octagon_holds

theorem idU3L2_of_gaps
    (hZ86 : Str86ZNotLe) : IdU3L2 :=
  idU3L2_of_zNotLe hZ86 weiss80UnitaryQuadrangle_holds

end CFSG.Quasithin.Stroth

end
