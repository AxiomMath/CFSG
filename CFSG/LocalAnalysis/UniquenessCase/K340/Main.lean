module

public import CFSG.LocalAnalysis.UniquenessCase.UC1S3Defs340
import CFSG.LocalAnalysis.UniquenessCase.K340.Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

theorem k340_holds : K340 :=
  fun _ _ _ _ _ _ _ _ _ _ hF hL hL2 hT hH hTLQ hZ hFdef hVdef hFJ hVJ hXN hXJ =>
    Campbell340.campbell_theoremA hF hL hL2 hT hH hTLQ hZ hFdef hVdef hFJ hVJ hXN hXJ

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

end
