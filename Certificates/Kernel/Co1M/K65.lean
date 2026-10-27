module

public import Certificates.Kernel.Co1M.D10065
public import Certificates.Data.Kernel.Co1M.Vtx10065
public import Certificates.Data.Kernel.Co1M.Graph65
public import CFSG.Sporadic.Co2Cert.Lit
public import Certificates.Kernel.VecCert.Co1.Data
public import CFSG.Certificates.Kernel.Co1M.OrbitMem
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1.Module.Forms

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Graph65 CFSG.KC.Co1M CFSG.KC.VecK CFSG.KC.InvFam CFSG.KC.SortTree
  CFSG.KLie.CT CFSG.KC.Co1F2 CFSG.Sporadic.Co1.Module.Pairs

@[expose] noncomputable def labK65 (w : Nat) : Nat :=
  if w = 0 then 0 else if q0N w then 2 else
    if orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 w then 3 else 1

theorem k65_eqv0 : eqvK (getL 0 RT65 (getL 0 G65 0)) (recT vtxL65 6 24) 2300
    CFSG.Sporadic.Co2Cert.co2G0 0 = true := by quickRfl

theorem k65_eqv1 : eqvK (getL 0 RT65 (getL 0 G65 1)) (recT vtxL65 6 24) 2300
    CFSG.Sporadic.Co2Cert.co2G1 0 = true := by quickRfl

theorem k65_vert : vertK (orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17)
    (recT vtxL65 6 24) 2300 = true := by quickRfl

theorem k65_dist : sortK (recT vtxL65 6 24) (recT ksL65 6 36) 2300 = true := by quickRfl

theorem k65_adj : andB (adjB labK65 (Nat.xor (recT vtxL65 6 24 0) (recT vtxL65 6 24 3)))
    (notB (adjB labK65 (Nat.xor (recT vtxL65 6 24 0) (recT vtxL65 6 24 1)))) = true := by
  quickRfl

end CertificateChecks.KernelCo1M

end
