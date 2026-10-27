module

public import Certificates.Kernel.Co1SevenK.CenData
public import Certificates.Data.Kernel.Co1Seven.Cen
public import Certificates.Data.Kernel.SporSch.Co1Bfs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KC.Co1B Timmesfeld.Co1Seven

@[expose] noncomputable def GB (l : Nat) : Nat := D.M ((Inst7.gens instB).getD l (nat_lit 0))

@[expose] noncomputable def TB : Nat := D.M (Inst7.xi instB)

theorem kGB : bAnd(Nat.beq (Inst7.gens instB).length (nat_lit 2), commGK GB 2 TB) = true := by
  quickRfl

theorem kTB : bAnd(Nat.beq CB.N (nat_lit 1176),
    gtPinK GB 2 100000 CB.N CB.P CB.PAR CB.LAB CB.W CB.S) = true := by quickRfl

theorem kFB : closK CB.P CB.N FB.R FB.C FB.W = true := by quickRfl

end CertificateChecks.KernelCo1SevenK

end
