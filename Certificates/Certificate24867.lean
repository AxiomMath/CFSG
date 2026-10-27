module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6InvCheck
public import Certificates.Certificate11003

public section

namespace CertificateChecks.Batch24867

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem sym6ConjData_0 : CFSG.EvenSporadicStandard.M24Std.Sym6.Sym6ConjData := by
  decide +kernel

end CertificateChecks.Batch24867

namespace Certificates

open CertificateChecks

theorem certificate24867 : CFSG.EvenSporadicStandard.M24Std.Sym6.Sym6ConjData := by
  exact CertificateChecks.Batch24867.sym6ConjData_0

end Certificates
