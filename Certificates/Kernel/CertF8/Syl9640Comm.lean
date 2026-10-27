module

public import Certificates.Kernel.CertF8.Syl9640Data
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

#kc_each CFSG.KC.CertF8.S9640.ch9640c c
  (fun k => CFSG.KC.Misc.Clos.allR (Nat.mul 81 (Nat.mod k 9)) 81
    (CFSG.KC.CertF8.S9640.repAt CFSG.KC.CertF8.S9640.T (Nat.div k 9))) 0 72

end
