module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData

public section

open CFSG.AGLEmbedding.KFactProofs.Sp62Local

namespace CertificateChecks.Batch9442

open CFSG.AGLEmbedding.KFactProofs.Sp62Local

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem chk_rel : chkRel = true := by
  decide +kernel

end CertificateChecks.Batch9442

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Sp62Local in
theorem certificate9442 : chkRel = true := by
  exact CertificateChecks.Batch9442.chk_rel

end Certificates
