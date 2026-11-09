module

public import CFSG.GH74.GLS.C3.Layer1.St1P89A6Data
import CFSG.Certificates.Kernel.PermCent.FastDecide

public section

namespace Certificates

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 1000000 in
open scoped CFSG.Certificates.Kernel.PkCV.FastDecide in
open CFSG.GH74.GLS.C3.Layer1.P89 in
theorem certificate5146 : CFSG.GH74.GLS.C3.Layer1.P89.P89Facts := by
  unfold P89Facts P89F1 P89F2 P89F3 P89F4 P89F5 P89Cond P89CondP P89CondX P89CondF P89CondB
    P89CondK P89Indep P89Span
  decide +kernel

end Certificates

