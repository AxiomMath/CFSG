module

public import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelCo1B.Cent27207

@[expose] def centText : String :=
  include_str "../../../CFSG/LocalAnalysis/EvenSporadicStandard/Induction/Rows/Co1CentTbl.txt"

end CertificateChecks.KernelCo1B.Cent27207

set_option maxRecDepth 400000 in
#ks_chars CertificateChecks.KernelCo1B.Cent27207.CT CertificateChecks.KernelCo1B.Cent27207.centText

end
