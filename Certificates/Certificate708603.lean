module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallClosed
import Certificates.Kernel.TwoNodeSmall.Assembly

public section

namespace Certificates

theorem certificate708603 : 
    ∀ P ∈ CFSG.TwoNodeSmall.pts8 () ++ CFSG.TwoNodeSmall.pts9 () ++
      CFSG.TwoNodeSmall.pts9m (), ∀ [Fact P.p.Prime], P.Closed :=
  CFSG.KD.TNS708603.closed_all

end Certificates
