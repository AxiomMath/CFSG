module

public import Certificates.Kernel.CertF8.Om9558Data
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

#kc_each CFSG.KC.CertF8.Om9558.ch9558s c
  (fun k => CFSG.KC.CertF8.Om.allFrom (Nat.mul 511 k) 511
    (CFSG.KC.CertF8.Om.sortAt CFSG.KC.CertF8.Om9558.F CFSG.KC.CertF8.Om9558.S 130816)) 128 256

end
