module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
import Certificates.Kernel.SporCovBase.McLThreeGlue

public section

namespace Certificates

theorem certificate1023403 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 3 CFSG.Blueprint.NativeSporadic.McL := by
  intros
  exact @CFSG.StandardType.SporadicShape.SporKRestCover.of_mulEquiv ↥CFSG.Sporadic.McL.J
    CFSG.Blueprint.NativeSporadic.McL inferInstance inferInstance CFSG.Sporadic.McL.mclEquivJ.symm 3
    CFSG.KD.SporCovBase.McLThree.sporKRestCover_three_J

end Certificates
