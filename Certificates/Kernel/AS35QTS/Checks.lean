module

public import Certificates.Data.Kernel.AS35QTS.Planes
public import Certificates.Kernel.AS35QTS.Data

public section

set_option profiler true
set_option profiler.threshold 200

namespace CFSG.KC.AS35QTS

open CFSG.KD.AS35QTS

theorem ch21280g : gOK G = true := by decide +kernel

theorem ch21280s : slOK G S = true := by decide +kernel

end CFSG.KC.AS35QTS

end
