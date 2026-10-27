
module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6DepAllDefs
import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6DepFinalBase
import Certificates.Kernel.ReflExt.MovAssembly

public section

namespace Certificates

theorem certificate708608 : CFSG.StandardType.LR6E6DepAll :=
  CFSG.StandardType.lr6E6DepAll_of_frame CFSG.KD.MK708608.e6dep_frame

end Certificates
