module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3Bridge
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3Toral
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3Datum
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DatumNo
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3Lattice
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3F4Sound
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3E6Sound
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim

public section

namespace CFSG.StandardType.LieCore

theorem ggSixA3ConjKnownTags_of_lieCore
    (hB : GGLieBridge) (hN : GGLieE6NonToralNoA8) (hC6 : GGLieCentIIPlane3 .E6)
    (hCF : GGLieCentIIPlane3 .F4) (hA6 : GGLieSmallFormA8Plane3 .E6)
    (hAF : GGLieSmallFormA8Plane3 .F4) (hE6 : GGLieA3DatumE6) :
    GGSixA3ConjKnownTags :=
  ggSixA3ConjKnownTags_of_alg hB <| ggLieA3Alg_of_toral hN <|
    ggLieA3AlgToral_of_datum hC6 hCF hA6 hAF
      (ggLieA3DatumNo_of_lattice
        (ggLieA3LatticeNo_of_spec a3SpecF4_of_certificate a3SpecTwE6_of_certificate)) hE6

end CFSG.StandardType.LieCore
