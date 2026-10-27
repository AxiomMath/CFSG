module

public import CFSG.LocalAnalysis.StandardType.GGForkAffineExcl
public import CFSG.LocalAnalysis.StandardType.GGForkCells

public section

namespace CFSG.StandardType

theorem ggForkAffineExclRest_of_tbFix (hFix : GGTBFixInput) : GGForkAffineExclRest :=
  ggForkAffineExclRest_of_tbSpan (ggTBSpanInput_of_fix hFix)

theorem ggTBFixInput_imp_forkLabel_split (hM : GGForkCrossGe5MainInput)
    (hE : GGForkCrossGe5ExcInput) (hI : GGForkIndefExclRest) :
    GGTBFixInput → GGCoxeterForkLabelInput := fun hFix =>
  ggCoxeterForkLabelInput_of_cells hFix (ggForkCrossGe5Input_of_f1_split hFix hM hE)
    (ggForkAffineExclRest_of_tbFix hFix) hI

end CFSG.StandardType
