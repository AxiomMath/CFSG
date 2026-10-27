module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosClosed
import Certificates.Kernel.TwoNodeSmall.PosBAssembly

public section

namespace Certificates

theorem certificate708601 : 
    ∀ Q ∈ CFSG.TwoNodeSmall.posBPts (), ∀ [Fact Q.pt.p.Prime], Q.ClosedPosB :=
  CFSG.KD.TNS708601.posB_closed_all

end Certificates
