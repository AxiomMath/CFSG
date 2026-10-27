module

public import CFSG.Quasithin.Recognition.HSType17k
public import CFSG.Quasithin.H13.KGFactM22Index
public import CFSG.Quasithin.H13.NQCatL34AutGraphField

public section

namespace CFSG.Quasithin.HSType

theorem statementI48_holds :
    StatementI48 :=
  statementI48_of_facts CFSG.Quasithin.H13.NQCat.L34Aut.factAutL34_holds
      CFSG.Quasithin.H13.NQCat.L34Aut.factAutL34GraphField_holds
      CFSG.Quasithin.H13.KGM22.factM22SubgroupIndex_holds

end CFSG.Quasithin.HSType
