module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosClosed
import Certificates.Kernel.TwoNodeSmall.ExclAssembly

public section

namespace Certificates

theorem certificate708602 : ∀ Q ∈ CFSG.TwoNodeSmall.exclPts (), ∀ [Fact Q.pt.p.Prime], Q.ClosedExcl :=
  CFSG.KD.TNS708602.excl_closed_all

end Certificates
