module

public import Certificates.Data.E8FiveStab
import Certificates.Kernel.E8Five.Checks
import CFSG.Certificates.Kernel.E8Five.Sound

open CFSG.KC.E8Five CertificateChecks.KernelE8Five

public section

namespace Certificates

open CFSG.RankThree.PartOne.KE8F in
theorem certificate14975 : E8FiveSylowCount :=
  sylowCount_of_checks ch14975kF1 ch14975kF2

end Certificates
