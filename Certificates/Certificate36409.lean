module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerFacts
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerDefs
import Certificates.Kernel.Tower.SlTower

public section

namespace Certificates

open CFSG.OddStandard.AltStdSmall4.Tower in
theorem certificate36409 : TowerFacts (Grp slS) (t₀ slS z0_mem_slS) :=
  KernelTower.towerFacts_sl

end Certificates
