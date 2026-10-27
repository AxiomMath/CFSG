module

public import Certificates.Data.Kernel.AS35QTS.Lens
public import Certificates.Kernel.AS35QTS.Data

public section

namespace CFSG.KC.AS35QTS

open CFSG.KD.AS35QTS

theorem ch21280_lens : lensOK G S IL W V0 = true := by decide +kernel

end CFSG.KC.AS35QTS

end
