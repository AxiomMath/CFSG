module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerFacts
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerDefs
import Certificates.Kernel.Tower.WrTower

public section

namespace Certificates

open CFSG.OddStandard.AltStdSmall4.Tower in
theorem certificate36408 : TowerFacts (Grp wrS) (t₀ wrS z0_mem_wrS) :=
  KernelTower.towerFacts_wr

end Certificates
