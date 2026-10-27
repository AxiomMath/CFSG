module

public import Certificates.Kernel.Co1Syl5.Dag
public import Certificates.Kernel.Co1Syl5.Bfs
public import Certificates.Data.Kernel.SporSch.Co1Cen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Syl5

open CFSG.KS.SporSch.M24 CFSG.KC.Co1B

@[expose] noncomputable def GA (l : Nat) : Nat := nIf(Nat.beq l (nat_lit 0), S.M 40, S.M 38)

theorem kQ : gtPinK GA 2 700 T.N T.P T.PAR T.LAB T.W T.S = true := by quickRfl

theorem kT : Nat.beq T.N 625 = true := by quickRfl

theorem kZ : cenK (S.M 40) (S.M 38) (S.M 41) T.N T.P = true := by quickRfl

theorem kX : eqK (powWK (S.M 41) 5) oneK = true := by quickRfl

end CertificateChecks.KernelCo1Syl5

end
