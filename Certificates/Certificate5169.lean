module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData
import Certificates.Kernel.Sp62L.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.Quasithin.G2U in
theorem certificate5169 : allCheck (fun x => !(commB x cSg) || inZ x) (tabOf gensB 27) = true :=
  KernelSp62L.check5169

end Certificates
