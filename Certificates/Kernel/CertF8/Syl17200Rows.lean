module

public import Certificates.Kernel.CertF8.Syl17200Data
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

#kc_each CFSG.KC.CertF8.S17200.ch17200r c
  (fun k => CFSG.KC.Misc.Clos.allR (Nat.mul 9 k) 9
    (CFSG.KC.CertF8.S17200.rowAt CFSG.KC.CertF8.S17200.T)) 0 27

namespace CFSG.KC.CertF8.S17200

theorem ch17200m : miscOK T = true := by
  decide +kernel

end CFSG.KC.CertF8.S17200

end
