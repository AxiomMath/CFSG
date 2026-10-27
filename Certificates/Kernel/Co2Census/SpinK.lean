module

public import Certificates.Kernel.Co2Census.SpinData
public import Certificates.Kernel.Co2Census.S0Defs
public import Certificates.Kernel.Co2SmithS.OrbK
public import Certificates.Data.CFSGNative.Co2Smith.Spin8

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2Census CFSG.Sporadic.Co2Smith.Native CertificateChecks.KernelCo2SmithS

theorem lsp_ok : (List.range 16).all (fun k => lspF k == rowsP ((spinMats ())[k]!)) = true := by
  decide +kernel

theorem ab_ok : (SpJ.ASP == wordRP lspF ((sp6Wa ()).map sCode) &&
    SpJ.BSP == wordRP lspF ((sp6Wb ()).map sCode)) = true := by
  decide +kernel

theorem gsp_ok : ((List.range 6).all fun k => (List.range ((chainGens ())[k]!).size).all fun l =>
    gspF k l == wordRP abF (((chainGens ())[k]!)[l]!)) = true := by
  decide +kernel

theorem tsp_ok : ((List.range 6).all fun k => tspF (trOff k) == idRP &&
    (List.range (chainOrb[k]!)).all fun i => Nat.beq i 0 ||
      tspF (trOff k + i) == mulRP (gspF k (PI (k + 1) 1 i)) (tspF (trOff k + PI (k + 1) 0 i))) =
    true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
