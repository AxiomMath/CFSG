module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3Assembly
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DatumE6
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3LatticeE6Alg

public section

namespace CFSG.StandardType.LieCore

theorem ggLieA3DatumE6_of_certificate :
    GGLieA3DatumE6 :=
  ggLieA3DatumE6_of_lattice ggLieA3LatticeE6_of_certificate

theorem ggSixA3ConjKnownTags_of_certificates
    (hB : GGLieBridge) (hN : GGLieE6NonToralNoA8) (hC6 : GGLieCentIIPlane3 .E6)
    (hCF : GGLieCentIIPlane3 .F4) (hA6 : GGLieSmallFormA8Plane3 .E6)
    (hAF : GGLieSmallFormA8Plane3 .F4) :
    GGSixA3ConjKnownTags :=
  ggSixA3ConjKnownTags_of_lieCore hB hN hC6 hCF hA6 hAF ggLieA3DatumE6_of_certificate

end CFSG.StandardType.LieCore
