module

public import CFSG.Milestones.ASVolI.F48.Small.Sp42Inputs

public section

open CFSG CFSG.ASVolI

namespace Certificates

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
open CFSG CFSG.ASVolI in
theorem certificate7531 : burnsideF48s_sp42PermFacts := by
  unfold burnsideF48s_sp42PermFacts
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Certificates
