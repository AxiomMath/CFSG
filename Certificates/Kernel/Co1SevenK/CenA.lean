module

public import Certificates.Kernel.Co1SevenK.CenData
public import Certificates.Data.Kernel.Co1Seven.Cen
public import Certificates.Data.Kernel.SporSch.Co1Bfs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KC.Co1B Timmesfeld.Co1Seven

@[expose] noncomputable def GA' (l : Nat) : Nat := D.M ((Inst7.gens instA).getD l (nat_lit 0))

@[expose] noncomputable def BA : Nat := D.M (Inst7.xi instA)

theorem kGA : bAnd(Nat.beq (Inst7.gens instA).length (nat_lit 2), commGK GA' 2 BA) = true := by
  quickRfl

theorem kTA : bAnd(Nat.beq CA.N (nat_lit 17640),
    gtPinK GA' 2 100000 CA.N CA.P CA.PAR CA.LAB CA.W CA.S) = true := by quickRfl

end CertificateChecks.KernelCo1SevenK

end
