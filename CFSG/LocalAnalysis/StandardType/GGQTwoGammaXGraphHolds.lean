module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraphLin
import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraphCore
import CFSG.LocalAnalysis.StandardType.GGQTwoGraphDn
import CFSG.LocalAnalysis.StandardType.GGQTwoGraphD4
import CFSG.LocalAnalysis.StandardType.GGQTwoGraphF4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2GraphCoreAll_holds : GGQ2GraphCoreAll :=
  ggQ2GraphCoreAll_of_abs (fun _ hn => ggQ2GraphAbsCore_D hn) ggQ2GraphAbsCore_D4
    ggQ2GraphAbsCore_F4

theorem ggQ2_gammaXOffI1Graph_of_tbc (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hTBC : GGQ2TBCGraphInput) : GGQ2GammaXOffI1GraphInput :=
  ggQ2_gammaXOffI1Graph_of_core hLB hP ggQ2GraphCoreAll_holds hTBC

end CFSG.StandardType

end
