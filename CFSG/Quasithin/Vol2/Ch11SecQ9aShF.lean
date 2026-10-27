module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aShE
public import CFSG.Quasithin.Vol2.Ch11SecQ9aG2C
public import CFSG.Quasithin.Vol2.Ch11SecQ9aG2D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS


theorem factParabTwo_holds : FactParabTwo :=
  factParabTwo_of_g2 factG2FourParabNonsolv_holds

theorem factParabGen_holds : FactParabGen :=
  factParabGen_of_g2 factG2FourParabNonsolv_holds

theorem factBorelShape_holds : FactBorelShape :=
  factBorelShape_of_g2 factG2FourParabNonsolv_holds factG2FourBorelNorm_holds

end CFSG.Quasithin.Vol2.Ch11.SecS
