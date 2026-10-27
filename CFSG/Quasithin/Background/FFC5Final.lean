module

public import CFSG.Quasithin.Background.FFC5Tail
public import CFSG.Quasithin.Background.B56Main

public section

namespace CFSG.Quasithin

namespace FFC

theorem asB56_of_inputs
    (hP4 : AsB15Part4) (hB51 : AsB51) (hA21 : AsA21SQTKSection)
    (h59 : AsB59) (hOff : B510OffendersAll) : AsB56 :=
  fun V _ _ hV G hne hB =>
    B56.asB56_of_lemmas hP4 asB58 h59 (asB5610_of_offenders hP4 hB51 hA21 hOff) V hV G hne hB

end FFC

end CFSG.Quasithin
