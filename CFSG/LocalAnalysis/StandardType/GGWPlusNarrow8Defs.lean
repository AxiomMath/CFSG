module

public import CFSG.LocalAnalysis.StandardType.GGWPlusNarrow7Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGL48TableBKnownFormsRestRkOpen8 : Prop :=
  GGL48TBForm1 ∧ GGL48TBForm2 ∧ GGL48TBForm4 ∧ GGL48TBForm5

end CFSG.StandardType
