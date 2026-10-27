module

public import Certificates.Kernel.CertF8.Syl17200Data
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

#kc_each CFSG.KC.CertF8.S17200.ch17200h c
  (fun k => CFSG.KC.Misc.Clos.allR (Nat.mul 27 k) 27
    (CFSG.KC.CertF8.S17200.h3At CFSG.KC.CertF8.S17200.T)) 0 9

end
