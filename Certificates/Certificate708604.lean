
module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6AllDefs
import CFSG.LocalAnalysis.StandardType.GGReflExtE6Base
import Certificates.Kernel.ReflExt.Assembly

public section

namespace Certificates

theorem certificate708604 : CFSG.StandardType.LR6E6All :=
  CFSG.StandardType.lr6E6All_of_frames CFSG.KD.RX708604.e6_frame0 CFSG.KD.RX708604.e6_frame1
    CFSG.KD.RX708604.e6_frame2

end Certificates
