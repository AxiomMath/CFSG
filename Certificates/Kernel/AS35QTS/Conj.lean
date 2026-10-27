module

public import Certificates.Data.Kernel.AS35QTS.Checks
public import Certificates.Kernel.AS35QTS.Data

public section

set_option profiler true
set_option profiler.threshold 200

namespace CFSG.KC.AS35QTS

open CFSG.KD.AS35QTS

theorem ch21280_il : ilOK G IL = true := by decide +kernel

theorem ch21280_qpow : qpowOK G = true := by decide +kernel

theorem ch21280_root : rootOK G IL R = true := by decide +kernel

theorem ch21280_inv : invOK G IL S INV = true := by decide +kernel

theorem ch21280_class : classOK G S CLS = true := by decide +kernel

theorem ch21280_ord : ordOK G S = true := by decide +kernel

theorem ch21280_line : lineOK G S LN CM = true := by decide +kernel

theorem ch21280_nz : nzOK G S IL W = true := by decide +kernel

theorem ch21280_nw : nwOK G S W V0 LN = true := by decide +kernel

theorem ch21280_swap : swapOK G S IL CM = true := by decide +kernel

theorem ch21280_cent : centOK G S = true := by decide +kernel

theorem ch21280_center : centerOK G = true := by decide +kernel

end CFSG.KC.AS35QTS

end
