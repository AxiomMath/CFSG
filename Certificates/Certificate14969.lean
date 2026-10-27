
module

public import Certificates.Data.HNUnitaryBridge
public import CFSG.RankThree.PartOne.HNB.F25
public import CFSG.Open.StatedDefs
public import CFSG.Monster.B.Co2.PermArr
import Certificates.Kernel.HN14969.Final
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace Certificates

open CertificateChecks

theorem certificate14969 : Nonempty (Subgroup.closure (Set.range fun k : Fin 6 =>
      CFSG.Monster.B.Co2.permOfArr 50 HNUnitaryBridge.smallPerms[(k : ℕ)]!) ≃*
    CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (5 ^ 1) CFSG.RankThree.PartOne.HNB.F25)) :=
  KernelHN14969.nonempty_mulEquiv

end Certificates
