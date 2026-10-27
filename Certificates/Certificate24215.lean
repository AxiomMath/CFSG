module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.ZData

public section

namespace Certificates

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certificate24215 : decide CFSG.EvenSporadicStandard.ThStd.LocalDataTh.HZFacts = true :=
  by decide +kernel

end Certificates
