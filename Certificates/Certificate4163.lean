module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuY2Inputs
import Certificates.Kernel.LocalQT.Quot.F4163

public section

namespace Certificates

open CFSG.Quasithin.A312Ru in
open CFSG.Sporadic.Ru.Native (ruData) in
theorem certificate4163 : OddGenOK ruData.n ruQuotL2 ruQuot2 ruQuot2Words := CFSG.KD.LQT.C4163.odd_ok

end Certificates
