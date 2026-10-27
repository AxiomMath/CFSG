module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
import Certificates.Kernel.Co1Three.Cover
public import CFSG.Sporadic.Schreier.Co1ThreeLocal

public section

namespace Certificates

theorem sporKRestCover_Co1_three :
    CFSG.StandardType.SporadicShape.SporKRestCover 3 CFSG.Blueprint.NativeSporadic.Co1 :=
  @CFSG.StandardType.SporadicShape.SporKRestCover.of_mulEquiv ↥CFSG.Sporadic.Co1Schreier.GA
    CFSG.Blueprint.NativeSporadic.Co1 (Subgroup.toGroup CFSG.Sporadic.Co1Schreier.GA) inferInstance
    CFSG.Sporadic.Co1Block.co1MatEquiv.symm 3 CertificateChecks.KernelCo1Three.cover

theorem certificate1023015 :     CFSG.StandardType.SporadicShape.SporKRestCover 3 CFSG.Blueprint.NativeSporadic.Co1 :=
  sporKRestCover_Co1_three

end Certificates
