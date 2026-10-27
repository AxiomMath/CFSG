module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutNodesCheckInputs
import Certificates.Kernel.LocalQT.HSAut.F4146

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.Id2519.HSAut in
open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native CFSG.QuasithinUnique.Id2519.UHS in
theorem certificate4146 : (nodesCheck = true) :=
  CFSG.KD.LQT.HN.nodes_check

end Certificates
