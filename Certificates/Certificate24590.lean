module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J2Check

public section

namespace CertificateChecks.Batch24590

private theorem j2SylowCheck_0 : CFSG.EvenSporadicStandard.Fin76b.J2.j2SylowCheck = true := by
  decide +kernel

end CertificateChecks.Batch24590

namespace Certificates

open CertificateChecks

theorem certificate24590 : CFSG.EvenSporadicStandard.Fin76b.J2.j2SylowCheck = true := by
  exact CertificateChecks.Batch24590.j2SylowCheck_0

end Certificates
