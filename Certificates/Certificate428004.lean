module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432D4TwoData
public import CFSG.RankThree.PartTwo.Sec4.RonanK432WitFact
import Certificates.Kernel.RonanWit.D4

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.RonanK432 in
theorem certificate428004 : WitFact d4WitData :=
  KernelRonanWit.D4.fact

end Certificates
