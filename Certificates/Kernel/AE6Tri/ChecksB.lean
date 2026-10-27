module

public import Certificates.Data.Kernel.AE6Tri.DefsB
public import Certificates.Kernel.AE6Tri.Data
public import Certificates.Kernel.AE6Tri.DataB
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.AE6Tri CFSG.KD.AE6Tri

theorem kInvD : invDOK RG (dg.getD 0 []) (vl.getD 0 []) (delta.getD 0 []) = true := by quickRfl

theorem kTGen : tgOK RG tg0 el tgW = true := by quickRfl

theorem kSep : allIx tzB (fun l b => sepOK RG 93 (tzP.getD l 0) (tzH.getD l []) b (tzO.getD l []))
    0 = true := by quickRfl

theorem kLev : allIx tzB (fun l b => levOK RG 93 (tzB.take l) b (tzW.getD l [])) 0 = true := by
  quickRfl

theorem kLevLen : (tzW.map List.length = [64, 32, 6]) ∧ tzB = [0, 172, 36] := by decide

end CertificateChecks.KernelAE6Tri

end
