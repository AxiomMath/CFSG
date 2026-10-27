module

public import Certificates.Data.Item434SporHe
import Certificates.Kernel.Item434Gen.HeFinal

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434SporGen in
theorem certificate9564 : heCheck = true :=
  KernelItem434.He.heCheck_true

end Certificates
