module

public import Certificates.Kernel.CertF8.Syl9640Data
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

#kc_each CFSG.KC.CertF8.S9640.ch9640r c
  (fun k => CFSG.KC.Misc.Clos.allR (Nat.mul 27 k) 27
    (CFSG.KC.CertF8.S9640.rowAt CFSG.KC.CertF8.S9640.T)) 0 27

namespace CFSG.KC.CertF8.S9640

theorem ch9640g : gensOK T = true := by
  decide +kernel

end CFSG.KC.CertF8.S9640

end
