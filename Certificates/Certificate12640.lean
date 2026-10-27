module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.U43ExtCheck

public section

open CFSG.AGLEmbeddingD2.Wilson.Coordinator.U43

namespace Certificates

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certificate12640 : CFSG.AGLEmbeddingD2.Wilson.Coordinator.U43.uExtCheck = true := by
  decide +kernel

end Certificates
