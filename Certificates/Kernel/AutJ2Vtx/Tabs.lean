module

public import Certificates.Kernel.AutJ2Vtx.Tbl
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelAJV

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.ComponentClassification.J2Cover

@[expose] noncomputable def abuL (l : Nat) : Nat := AJT (Nat.add l 2)

@[expose] noncomputable def sylL (l : Nat) : Nat := AJT (Nat.sub l 1)

@[expose] noncomputable def q2L (l : Nat) : Nat := AJT (Nat.add l 7)

@[expose] noncomputable def s1L (l : Nat) : Nat := nIf(Nat.ble l 3, AJT (Nat.sub l 1), AJT 7)

@[expose] noncomputable def wK (L : Nat → Nat) (w : List Nat) : Nat :=
  wfoldK 315 9 (mask 9) L w (pidn 315 9)

theorem binds_ok : bAnd(bindListK 315 9 (AJT 0) (sylowStrong.getD 0 #[]).toList,
    bAnd(bindListK 315 9 (AJT 1) (sylowStrong.getD 1 #[]).toList,
    bAnd(bindListK 315 9 (AJT 2) (sylowStrong.getD 2 #[]).toList,
    bAnd(bindListK 315 9 (AJT 3) (autStrong.getD 0 #[]).toList,
    bAnd(bindListK 315 9 (AJT 4) (autStrong.getD 1 #[]).toList,
    bindListK 315 9 (AJT 5) outerArr.toList))))) = true := by
  quickRfl

theorem words_ok :
    bAnd(Nat.beq (AJT 6) (wK abuL [2, 3, 1, 2, 2, 1, 3, 3, 3, 3, 3, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2,
      3, 3, 1]),
    bAnd(Nat.beq (AJT 7) (wK abuL [2, 3, 2]),
    bAnd(Nat.beq (AJT 8) (wK sylL [2, 3, 1, 3, 3, 3]),
    bAnd(Nat.beq (AJT 9) (wK sylL [1, 1, 3, 3, 3, 3]),
    bAnd(Nat.beq (AJT 10) (wK sylL [2, 1, 2, 1]),
    bAnd(Nat.beq (AJT 11) (wK sylL [2, 3, 3, 1]),
    bAnd(Nat.beq (AJT 12) (wK sylL [2]),
    bAnd(Nat.beq (AJT 13) (wK q2L [1, 1, 2]),
    bAnd(Nat.beq (AJT 14) (wK sylL [3, 1, 3, 1, 3, 3]),
    bAnd(Nat.beq (AJT 15) (wK sylL [1, 1, 1, 3, 2, 1]),
    bAnd(Nat.beq (AJT 16) (wK sylL [2, 1, 3, 2, 1, 3]),
    bAnd(Nat.beq (AJT 17) (wK sylL [1, 1, 1, 2, 3, 1]),
    bAnd(Nat.beq (AJT 18) (wK sylL [1, 1, 3, 1, 2, 3]),
    bAnd(Nat.beq (AJT 19) (wK sylL [1, 1, 1, 2, 1]),
    bAnd(Nat.beq (AJT 20) (wK s1L [2, 4, 3, 4, 2, 3]),
    Nat.beq (AJT 21) (wK s1L [3, 4, 3, 4, 1, 4])))))))))))))))) = true := by
  quickRfl

end CertificateChecks.KernelAJV

end
