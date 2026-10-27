module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreTags
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCorePSL
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmega
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreE6
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreE7
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreE8

public section

namespace CFSG.StandardType

theorem ggJRootCoreAt_E7 :
    GGJRootCoreAt .E7 :=
  ggJRootCoreAt_of_torus
    (fun _ f _ _ => CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot (K := GaloisField 2 f))
    (fun _ _ _ _ _ _ _ f ψ hloc b hb => PsiDiag.Minu.exists_mem_centralizer_E7
      (k := GaloisField 2 f) ψ hloc.2.1.1 (hloc.2.2.2.1 b hb))
    jcore_E7_torus

theorem ggJRootCoreAt_E8 :
    GGJRootCoreAt .E8 :=
  ggJRootCoreAt_of_torus
    (fun _ f _ _ => CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E8)
      (K := GaloisField 2 f))
    (fun _ _ _ _ _ _ _ f ψ hloc b hb => PsiDiag.Adj.exists_mem_centralizer_E8
      (K := GaloisField 2 f) ψ hloc.2.1.1 (hloc.2.2.2.1 b hb))
    jcore_E8_torus

theorem ggJRootCoreInput_holds :
    GGJRootCoreInput :=
  ggJRootCoreInput_of_tags ggJRootCoreAt_PSL ggJRootCoreAt_POmegaPlus ggJRootCoreAt_E6
    ggJRootCoreAt_E7 ggJRootCoreAt_E8

end CFSG.StandardType

end
