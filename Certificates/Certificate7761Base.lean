
module

public import CFSG.Milestones.ASVolI.F48.Rest.G23Defs
import CFSG.Milestones.ASVolI.F48.Rest.G23Faithful
import Certificates.Kernel.G23F48.PtsGlue

@[expose] public section

namespace Certificates

theorem certificate7761_card_X : Nat.card ↥CFSG.ASVolI.burnsideF48t_g23X = 4245696 :=
  CFSG.ASVolI.burnsideF48t_g23_card_X_of_frame (FI := fun i => CFSG.KC.G23F48.frameIdx[i]!)
    CFSG.KC.G23F48.frame_ok CFSG.KC.G23F48.frameIdx_lt CFSG.KC.G23F48.pts_frame

end Certificates
