module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeField

public section

namespace CFSG.StandardType

theorem ggEndNodeAdmUnitarySixThreeInput_holds :
    GGEndNodeAdmUnitarySixThreeInput :=
  TableBU63.ggEndNodeAdmUnitarySixThreeInput_of_fieldType TableBU63.fieldTypeEndNodeInput_holds

theorem ggEndNodeAdmUnitaryDvdInput_holds :
    GGEndNodeAdmUnitaryDvdInput :=
  ggEndNodeAdmUnitaryDvdInput_of_sixThree ggEndNodeAdmUnitarySixThreeInput_holds

end CFSG.StandardType
