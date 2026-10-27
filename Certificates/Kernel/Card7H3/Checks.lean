module

public import Certificates.Data.Kernel.Card7H3.CV

public section

namespace Certificates.Kernel.Card7H3

open CFSG.Certificates.Kernel.Card7H3 CFSG.Certificates.Kernel.PkCV
  CFSG.GH74.GLS.C3.Prop121.Card7.HC

set_option maxRecDepth 100000

theorem k5082a_true : k5082a = true := by decide +kernel

theorem k5082b_true : k5082b = true := by decide +kernel

theorem k5082c_true : k5082c = true := by decide +kernel

end Certificates.Kernel.Card7H3

end
