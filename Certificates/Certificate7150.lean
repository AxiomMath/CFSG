module

public import CFSG.Certificates.Kernel.Misc.L52Sound
public import CFSG.Certificates.Kernel.Misc.L52FastSound
public import Certificates.Kernel.Misc.L52.FastChecks

public section

open CFSG.Quasithin.H13.KGE64

namespace Certificates

open CFSG.Quasithin.H13.KGE64 in
theorem certificate7150 : l52Check = true :=
  CFSG.KC.L52.l52Check_eq.trans (CFSG.KC.L52.l52CheckN_of_F CFSG.KD.L52.l52CheckFN_ok)

end Certificates
