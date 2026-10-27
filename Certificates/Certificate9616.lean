module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanE6TwoSylowData
import Certificates.Kernel.ONanE6Two.Sylow9616

public section

namespace Certificates

open CFSG.AGLEmbedding.E6Two in
theorem certificate9616 : e6SylowCheck e6SylowData = true :=
  Kernel.ONanE6Two.e6SylowCheck_k9616

end Certificates
