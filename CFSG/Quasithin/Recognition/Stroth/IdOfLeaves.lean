module

public import CFSG.Quasithin.Recognition.Stroth.IdSzL2
public import CFSG.Quasithin.Recognition.Stroth.IdU3L2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.H13

theorem idSzL2W_of_leaves
    (hT : Str83LocTrans9) (hO : Str83Orders) (hK : Str83Kernel) (hW : Weiss80Octagon) :
    IdSzL2W :=
  idSzL2W_of_moufang (str83Moufang_of_leaves hT hO) hO hK hW

theorem idU3L2_of_leaves (hT : Str86LocTrans5) (hO : Str86Orders)
    (hW : Weiss80UnitaryQuadrangle) : IdU3L2 :=
  idU3L2_of_moufang (str86Moufang_of_leaves hT hO) hO hW

end CFSG.Quasithin.Stroth

end
