module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem11Borel
public import CFSG.Quasithin.H13.KGFact22TorusFacts
public import CFSG.Quasithin.Background.E6TorusCover

public section

namespace CFSG.Quasithin.H13

theorem lem12211Borel_of_e22 (hE : E2.E22StatementC) :
    Lem12211Borel :=
  lem12211Borel_of hE (E2.e22TorusCover_of_facts e22TorusFacts_holds)

end CFSG.Quasithin.H13
