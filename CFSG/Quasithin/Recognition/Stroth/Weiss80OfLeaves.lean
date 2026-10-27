module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80OctagonAssembly
public import CFSG.Quasithin.Recognition.Stroth.Weiss80UnitaryAssembly
public import CFSG.Quasithin.Recognition.Stroth.RootGroupLift
public import CFSG.Quasithin.Recognition.Stroth.StabilizersOfPolygon
public import CFSG.Quasithin.Recognition.Stroth.OctBorelResidualSplit
public import CFSG.Quasithin.Recognition.Stroth.QuadrangleIdentification
public import CFSG.Quasithin.Recognition.Stroth.SubconstUnitaryNonabelian
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.Recognition.Stroth.Un5BorelResidualSplit

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13

theorem weiss80Octagon_of_leaves
    (hRTS : MoufangRankTwoSystem 8) (hPoly : Weiss80Polygon8Fin)
    (hT : Tits83T8System) (hO : Tits83Orders) : Weiss80Octagon :=
  weiss80OctagonAssembly (weissEmbeddingFacts 8) (rootGroupRegular 8) hRTS
    (moufangLittleNormal 8) (stabilizersOfPolygon 8) extensionOfStabilizers
    borelResidualSplitTransport octBorelResidualSplit octLieModel hPoly hT hO subconstNatural

theorem weiss80UnitaryQuadrangle_of_leaves (hRTS : MoufangRankTwoSystem 4)
    (hPoly : Weiss80Polygon4Fin) (hHerm : FGQHermitianUnique) (hAb : FGQRootsAbelian) :
    Weiss80UnitaryQuadrangle :=
  weiss80UnitaryAssembly (weissEmbeddingFacts 4) (rootGroupRegular 4) hRTS
    (quadrangleIdentification_of_fgq hHerm hAb) (moufangLittleNormal 4) (stabilizersOfPolygon 4)
    extensionOfStabilizers borelResidualSplitTransport un5BorelResidualSplit hPoly hHerm hAb
    subconstNatural subconstUnitaryNonabelian

end CFSG.Quasithin.Stroth

end
