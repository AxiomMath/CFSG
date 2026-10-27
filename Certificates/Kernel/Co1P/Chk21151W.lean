module

public import Certificates.Kernel.Co1P.Defs21151
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.TreeK CFSG.Sporadic.Co1Patterson.Native

theorem walk4C_hs : (treePts (hsAct BK) 8 oneK (recsT orb4cMasks)).2 = true := by quickRfl

theorem walk4C_his : (treePts (hisAct BIK) 8 oneK (recsT orb4cMasks)).2 = true := by quickRfl

theorem walkF8_hs : (treePts (hsAct GE) 6 oneK (recsT fib8Masks)).2 = true := by quickRfl

theorem walkF8_his : (treePts (hisAct GEI) 6 oneK (recsT fib8Masks)).2 = true := by quickRfl

theorem walkF5_hs : (treePts (hsAct GZ) 6 oneK (recsT fib5Masks)).2 = true := by quickRfl

theorem walkF5_his : (treePts (hisAct GZI) 6 oneK (recsT fib5Masks)).2 = true := by quickRfl

end CertificateChecks.KernelCo1P

end
