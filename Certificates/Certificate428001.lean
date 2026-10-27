module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432TitsData
public import CFSG.RankThree.PartTwo.Sec4.RonanK432WitFact
import Certificates.Kernel.RonanWit.Tits

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.RonanK432 in
theorem certificate428001 : WitFact titsWitData :=
  KernelRonanWit.Tits.fact

end Certificates
