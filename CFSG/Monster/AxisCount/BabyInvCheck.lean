module

public import Certificates.Certificate6005

public section

namespace CFSG.Monster.AxisCount.Baby

theorem baby_inv_injective :
    Function.Injective fun j : Fin 10 => (xStarCoord (vv j), trA2 (vv j)) :=
  Certificates.certificate6005

end CFSG.Monster.AxisCount.Baby
