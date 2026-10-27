module

public import CFSG.CGT.T75JM.N6A6
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CFSG.KernelN6

open CFSG.CGT.T75JM

theorem a6Nodup_ok : A6Nodup := a6Nodup_of_check (by quickRfl)

end CFSG.KernelN6
