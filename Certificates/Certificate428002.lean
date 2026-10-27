module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432OmegaData
public import CFSG.RankThree.PartTwo.Sec4.RonanK432WitFact
import Certificates.Kernel.RonanWit.Omega

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.RonanK432 in
theorem certificate428002 : WitFact omWitData :=
  KernelRonanWit.Omega.fact

end Certificates
