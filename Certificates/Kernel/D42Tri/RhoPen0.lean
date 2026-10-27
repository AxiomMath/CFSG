module

public import Certificates.Kernel.D42Tri.RhoRec
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CertificateChecks.KernelD42Tri in
#kc_each CertificateChecks.KernelD42Tri ch17628pe_
  (fun s => penumSlK 360 9 (mask 9) (360 * 9) true RC.G RC.GI 8 RC.cnt RC.T RC.PL RC.POS RC.SRT
    RC.SRI (600 * s) 600) 0 6

end
