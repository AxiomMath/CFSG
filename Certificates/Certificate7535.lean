module

public import CFSG.Milestones.ASVolI.F48.Small.G22Inputs

public section

open CFSG CFSG.ASVolI

namespace Certificates

set_option maxHeartbeats 0 in
open CFSG CFSG.ASVolI in
theorem certificate7535 : burnsideF48s_g22CheckGens () = true ∧ burnsideF48s_g22CheckRels () = true ∧
    burnsideF48s_g22CheckLetters () = true ∧ burnsideF48s_g22CheckClosed () = true ∧
    burnsideF48s_g22CheckCand () = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Certificates
