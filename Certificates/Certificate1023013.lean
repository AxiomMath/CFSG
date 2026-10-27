module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
import Certificates.Kernel.Co1Seven.Cover
import CFSG.Sporadic.Co1Block.PermBase

public section

namespace Certificates

theorem sporKRestCover_Co1_seven :
    CFSG.StandardType.SporadicShape.SporKRestCover 7 CFSG.Blueprint.NativeSporadic.Co1 :=
  @CFSG.StandardType.SporadicShape.SporKRestCover.of_mulEquiv ↥CFSG.Sporadic.Co1Schreier.GA
    CFSG.Blueprint.NativeSporadic.Co1 (Subgroup.toGroup CFSG.Sporadic.Co1Schreier.GA) inferInstance
    CFSG.Sporadic.Co1Block.co1MatEquiv.symm 7 CertificateChecks.KernelCo1Seven.cover

theorem certificate1023013 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 7 CFSG.Blueprint.NativeSporadic.Co1 :=
  sporKRestCover_Co1_seven

end Certificates
