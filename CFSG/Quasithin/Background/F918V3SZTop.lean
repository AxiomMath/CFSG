module

public import CFSG.Quasithin.Background.F918V3Main
public import CFSG.Quasithin.Background.F918V3SZMain

public section

namespace CFSG.Quasithin

theorem d392_of_d38
    (h38 : D38Top) : D392 :=
  d392_of_suzuki (d392Suzuki_of_d38 h38)

end CFSG.Quasithin
