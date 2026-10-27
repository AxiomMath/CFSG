
module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineAllDefs
import CFSG.LocalAnalysis.StandardType.GGReflNineFinalBase
import Certificates.Kernel.ReflExt.NineAssembly

public section

namespace Certificates

theorem certificate708606 : CFSG.StandardType.LR6NineAll :=
  CFSG.StandardType.lr6NineAll_of_frames CFSG.KD.NK708606.nine_frame8
    CFSG.KD.NK708606.nine_frame9

end Certificates
