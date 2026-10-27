module

public import Certificates.Data.Item434SporRu
import Certificates.Kernel.Item434Gen.RuFinal

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434SporGen in
theorem certificate9565 : CFSG.RankThree.PartTwo.Sec4.Item434SporGen.ruCheck = true :=
  KernelItem434.Ru.ruCheck_true

end Certificates
