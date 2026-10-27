module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
import Certificates.Kernel.SporCovLane.HNGlue
public import CFSG.Sporadic.HNSchreier.Faithful

public section

namespace Certificates

theorem certificate1023012 :     CFSG.StandardType.SporadicShape.SporKRestCover 3 CFSG.Blueprint.NativeSporadic.HN := by
  intros
  exact @CFSG.StandardType.SporadicShape.SporKRestCover.of_mulEquiv
    ↥CFSG.Sporadic.HNSchreier.JH CFSG.Blueprint.NativeSporadic.HN inferInstance inferInstance
    CFSG.Sporadic.HNSchreier.hnEquivJ.symm 3 CFSG.KD.SporCovLane.HN.sporKRestCover_three_JH

end Certificates
