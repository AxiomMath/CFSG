module

public import Certificates.Kernel.Co1SevenK.SylData
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import Certificates.Data.Kernel.Co1BW
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.KC.Co1B Timmesfeld.Co1Seven

@[expose] noncomputable def SK : Nat := D.M iS

@[expose] noncomputable def TK : Nat := D.M iT

@[expose] noncomputable def GP (l : Nat) : Nat := nIf(Nat.beq l (nat_lit 0), SK, TK)

@[expose] noncomputable def xGK (k : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 0), SK, nIf(Nat.beq k (nat_lit 1), TK, mulWK TK (powWK SK (Nat.sub k (nat_lit 1)))))

@[expose] noncomputable def cK (k : Nat) : Nat :=
  strictN (fusG.getD k (nat_lit 0)) fun j => nIf(Nat.blt j D.N, D.M j, idM)

@[expose] noncomputable def tK (k : Nat) : Nat := nIf(Nat.beq (fusTgt.getD k (nat_lit 0)) (nat_lit 0), SK, TK)

theorem kP : bAnd(Nat.beq PT.N (nat_lit 49),
    gtPinK GP 2 100000 PT.N PT.P PT.PAR PT.LAB PT.W PT.S) = true := by quickRfl

theorem kS : (unpack 24 24 SK != unpack 24 24 idM && unpack 24 24 TK != unpack 24 24 idM &&
    Nat.beq (mulWK SK TK) (mulWK TK SK) && Nat.beq (powWK SK 7) idM &&
    Nat.beq (powWK TK 7) idM) = true := by quickRfl

theorem kC : allN PT.N (fun p => strictB (PT.P p) fun x => bIf(Nat.beq x idM, true,
    strictB (PC p) fun c => bAnd(Nat.blt c (nat_lit 48),
      Nat.beq x (powWK (xGK (Nat.div c (nat_lit 6))) (Nat.succ (Nat.mod c (nat_lit 6))))))) = true := by
  quickRfl

theorem kF : allN 8 (fun k => strictB (cK k) fun c =>
    Nat.beq (mulWK c (xGK k)) (mulWK (tK k) c)) = true := by quickRfl

end CertificateChecks.KernelCo1SevenK

end
