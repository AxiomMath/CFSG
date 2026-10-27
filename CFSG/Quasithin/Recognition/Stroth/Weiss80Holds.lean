module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80OfLeaves
public import CFSG.Quasithin.Recognition.Stroth.MoufangSystem
public import CFSG.Quasithin.Recognition.Stroth.Weiss80RootsAbelian
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Polygon4Fin
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Polygon8Fin
public import CFSG.GH74.Tits83.Orders
public import CFSG.GH74.Tits83.T8System
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Unique2

public section

namespace CFSG.Quasithin.Stroth


theorem weiss80Octagon_holds :
    Weiss80Octagon :=
  weiss80Octagon_of_leaves (moufangRankTwoSystem 8) WeissDelta.weiss80Polygon8Fin
    CFSG.GH74.Tits83.tits83T8System CFSG.GH74.Tits83.tits83Orders

theorem weiss80UnitaryQuadrangle_holds : Weiss80UnitaryQuadrangle :=
  weiss80UnitaryQuadrangle_of_leaves (moufangRankTwoSystem 4) WeissDelta.weiss80Polygon4Fin
    CFSG.Geometry.GeneralizedQuadrangles.fgqHermitianUnique fgqRootsAbelian

end CFSG.Quasithin.Stroth

end
