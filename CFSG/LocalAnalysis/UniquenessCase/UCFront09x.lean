module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09u
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09w
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R911
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5Proof
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R99
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R9R5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R922A5Proof
import CFSG.RankThree.PartTwo.KFacts.KS44Sz

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.AGLEmbedding (KFactCatalogSchreier)

variable {G : Type} [Group G] [Finite G]

theorem r923_holds_of_r913A5S
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hSch : KFactCatalogSchreier)
    (hKF : KFactShape92NoFaithfulA5) (hK : UCK.K332Cyc)
    (h63 : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixThreeCore) (D : Data G)
    (hSg : UC6S846.SigmaStd D) (h640 : UC6.R6_40_1 D) (h92 : R92 D) (h913 : R913A5S D) :
    R923 D :=
  r923_holds hG3 hSch hKF hK D hSg h92
    (r922A5_of_r917A5 CFSG.RankThree.PartTwo.KFacts.kpSz D (r912A5_of_inputs D (r99_holds D)
        (r910_holds D) (r911_of h63 D h640) (r9R5_holds D))
      (r917A5_of_r913A5S D (r912A5_of_inputs D (r99_holds D) (r910_holds D) (r911_of h63 D h640)
          (r9R5_holds D)) h913))

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
