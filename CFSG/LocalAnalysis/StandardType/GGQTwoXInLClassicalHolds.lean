module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFHolds
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameU
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLAmbLinear

public section

namespace CFSG.StandardType

theorem ggQTwoXInLNbrClassical_holds :
    GGQTwoXInLNbrClassical :=
  ggQTwoXInLNbrClassical_of_frames
    (fun _ _ _ _ _ _ _ _ _ hS hI hxL hA => ggQTwoXInL_frame_unitary hS hI hxL hA)
    ggQTwoXInL_frame_formed
    (fun _ _ _ _ _ _ _ _ _ hS hI hxL hA => ggQTwoXInL_ambient_linear_false hS hI hxL hA)

end CFSG.StandardType

end
