module

public import CFSG.LargeExtraspecial.AS35QTSFacts
import CFSG.Certificates.Kernel.AS35QTS.PlanesSound
import Certificates.Kernel.AS35QTS.Checks
import Certificates.Kernel.AS35QTS.Conj
import Certificates.Kernel.AS35QTS.Lens

public section

namespace Certificates

open CFSG.KC.AS35QTS in
theorem certificate21280 : CFSG.LargeExtraspecial.AS35QTS.QtsFacts :=
  qtsFacts_of ch21280g ch21280s ch21280_il ch21280_qpow ch21280_root ch21280_inv ch21280_class
    ch21280_ord ch21280_line ch21280_nz ch21280_nw ch21280_swap ch21280_cent ch21280_center
    ch21280_lens

end Certificates

end
