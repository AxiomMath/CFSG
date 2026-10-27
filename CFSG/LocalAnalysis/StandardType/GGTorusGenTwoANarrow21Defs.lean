module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcNarrow20Defs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenLinTwoNarrowDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGL48TableBKnownFormsRestRkOpen21 : Prop :=
  GGL48TBForm1Rest20 ∧ GGL48TBForm4RestTwoA ∧ GGL48TBForm5RowE

end CFSG.StandardType
