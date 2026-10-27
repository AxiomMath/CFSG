module

public import Certificates.Data.Kernel.AE6Tri.DefsTAT
public import Certificates.Kernel.AE6Tri.Data
public import Certificates.Kernel.AE6Tri.DataTAT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelAE6TriTA

open CFSG.KC.Enum CFSG.KC.AE6Tri CFSG.KD.AE6Tri CFSG.KD.AE6TAT

theorem kTat0 : tabEq RG (nthD tatA [] 0) (nthD tatB [] 0) (nthD tatCs [] 0) = true := by quickRfl

theorem kTat1 : tabEq RG (nthD tatA [] 1) (nthD tatB [] 1) (nthD tatCs [] 1) = true := by quickRfl

theorem kTat2 : tabEq RG (nthD tatA [] 2) (nthD tatB [] 2) (nthD tatCs [] 2) = true := by quickRfl

theorem kTat3 : tabEq RG (nthD tatA [] 3) (nthD tatB [] 3) (nthD tatCs [] 3) = true := by quickRfl

theorem kTat4 : tabEq RG (nthD tatA [] 4) (nthD tatB [] 4) (nthD tatCs [] 4) = true := by quickRfl

theorem kTat5 : tabEq RG (nthD tatA [] 5) (nthD tatB [] 5) (nthD tatCs [] 5) = true := by quickRfl

theorem kTat6 : tabEq RG (nthD tatA [] 6) (nthD tatB [] 6) (nthD tatCs [] 6) = true := by quickRfl

theorem kTat7 : tabEq RG (nthD tatA [] 7) (nthD tatB [] 7) (nthD tatCs [] 7) = true := by quickRfl

theorem kTat8 : tabEq RG (nthD tatA [] 8) (nthD tatB [] 8) (nthD tatCs [] 8) = true := by quickRfl

theorem kTat9 : tabEq RG (nthD tatA [] 9) (nthD tatB [] 9) (nthD tatCs [] 9) = true := by quickRfl

theorem kTat10 : tabEq RG (nthD tatA [] 10) (nthD tatB [] 10) (nthD tatCs [] 10) = true := by
  quickRfl

theorem kTat11 : tabEq RG (nthD tatA [] 11) (nthD tatB [] 11) (nthD tatCs [] 11) = true := by
  quickRfl

end CertificateChecks.KernelAE6TriTA

end
