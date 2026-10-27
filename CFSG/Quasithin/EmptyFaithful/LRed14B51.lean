module

public import CFSG.Quasithin.Background.SmithB51Assembly
public import CFSG.Quasithin.Background.SmithB51SL3Main

public section

namespace CFSG.Quasithin

namespace B5

theorem asB51_of_b42
    (hB42 : AsB42) : AsB51 :=
  asB51_of_open hB42 (asB51NonirrSL3Ind_holds hB42 asA21SQTKSection asA36NoOddCover_holds)

end B5

end CFSG.Quasithin
