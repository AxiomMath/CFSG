module

public import CFSG.Quasithin.Vol2.Ch11SecAKM7
public import CFSG.Quasithin.Vol2.Ch11SecAKM6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

theorem factModules3n_of_open (hSL3 : FactModulesSL3) (hA7 : FactHatA7Module) :
    FactModules3n :=
  factModules3n_of factList2Table_holds factList3Table_holds hSL3 hA7
    factModulesList3Order_holds factModulesList2Bang_holds

end CFSG.Quasithin.Vol2.Ch11.SecA
