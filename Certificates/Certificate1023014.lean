module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
import Certificates.Kernel.Co1Five.Cover
import CFSG.Sporadic.Co1Block.PermBase

public section

namespace Certificates

theorem sporKRestCover_Co1_five :
    CFSG.StandardType.SporadicShape.SporKRestCover 5 CFSG.Blueprint.NativeSporadic.Co1 :=
  @CFSG.StandardType.SporadicShape.SporKRestCover.of_mulEquiv ↥CFSG.Sporadic.Co1Schreier.GA
    CFSG.Blueprint.NativeSporadic.Co1 (Subgroup.toGroup CFSG.Sporadic.Co1Schreier.GA) inferInstance
    CFSG.Sporadic.Co1Block.co1MatEquiv.symm 5 CertificateChecks.KernelCo1Five.cover

theorem certificate1023014 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 5 CFSG.Blueprint.NativeSporadic.Co1 :=
  sporKRestCover_Co1_five

end Certificates
