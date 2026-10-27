module

public import Certificates.Kernel.CertF8.Om9558Data
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

#kc_each CFSG.KC.CertF8.Om9558.ch9558f c
  (fun k => CFSG.KC.CertF8.Om.allFrom (Nat.mul 511 k) 511
    (CFSG.KC.CertF8.Om.forestAt CFSG.KC.CertF8.Om9558.F)) 192 256

end
