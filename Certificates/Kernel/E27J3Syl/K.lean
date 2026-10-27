module

public import Certificates.Kernel.E27J3Syl.D
public import Certificates.Kernel.Census.J3.Text
public import Certificates.Data.Kernel.Spor.MulHCay
public import Certificates.Data.Kernel.Spor.HSortB
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.E27J3S

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.MulHCay

@[expose] noncomputable def jcn (p : Nat) : Bool := canonK 6156 13 (mask 13) (6156 * 13) p

@[expose] noncomputable def jiv (p r : Nat) : Bool :=
  bAnd(jcn p, bAnd(jcn r, invEqK 6156 13 (mask 13) (6156 * 13) p r))

@[expose] noncomputable def jc (p q : Nat) : Nat := pcomp 6156 13 (mask 13) p q

@[expose] noncomputable def jid : Nat := pidn 6156 13

@[expose] noncomputable def jA (l : Nat) : Nat := CertificateChecks.KernelCensus.J3S.F (Nat.sub l 1)

@[expose] noncomputable def jW (wd : List Nat) : Nat := wfoldK 6156 13 (mask 13) jA wd jid

@[expose] noncomputable def jWit (x a b : Nat) : Bool :=
  bAnd(Nat.beq (jc a x) (jc x a), bAnd(Nat.beq (jc b x) (jc x b),
  bAnd(Nat.beq (powPK 6156 13 (mask 13) a 2) jid, bAnd(Nat.beq (powPK 6156 13 (mask 13) b 3) jid,
  bAnd(Nat.beq (powPK 6156 13 (mask 13) (jc a b) 5) jid,
  bAnd(bIf(Nat.beq a jid, false, true), bIf(Nat.beq b jid, false, true)))))))

@[expose] noncomputable def c131001Base : Bool :=
  bAnd(allN 8 (fun k => jiv (SY.F k) (SYI k)),
  bAnd(allN 2 (fun k => jiv (CertificateChecks.KernelCensus.J3S.F k) (SGI k)),
  bAnd(jcn jid, bAnd(Nat.beq SE.k 2, bAnd(Nat.beq SE.cnt 243,
  bAnd(penumHdK jid SE.cnt 300 SE.T SE.PL,
  bAnd(allN 2 (fun j => bAnd(Nat.beq (SE.GI j) (SY.F j), bAnd(Nat.beq (SE.G j) jid,
    jiv (SE.GI j) (SEI j)))),
  allN 2 (fun c => strictB (r32 SEX c) (fun q => bAnd(Nat.blt q SE.cnt,
    Nat.beq (SE.T q) (SY.F (Nat.add 2 (Nat.mul 3 c)))))))))))))

@[expose] noncomputable def c131001Wit : Bool :=
  bAnd(jWit (SY.F 2) (SY.F 3) (SY.F 4), jWit (SY.F 5) (SY.F 6) (SY.F 7))

@[expose] noncomputable def c131001Cay (k : Nat) : Bool :=
  slK (Nat.mul 243 243) (cayPtK 243 2 SE.PL SE.POS SEM) (Nat.mul 4096 k) 4096

@[expose] noncomputable def jq (a b : Nat) : Nat := r32 SEM (Nat.add (Nat.mul 243 a) b)

@[expose] noncomputable def jEl (i : Nat) : Bool :=
  bIf(Nat.beq i 0, true, bIf(Nat.beq (jq i (jq i i)) 0,
    bIf(Nat.beq (Nat.mod (cntBelowK 243 (fun j => Nat.beq (jq j i) (jq i j)) 4) 81) 0, true,
      Nat.blt 0 (cntBelowK 243 (fun p => bIf(Nat.beq (jq p (r32 SEX 0)) (jq i p), true,
        Nat.beq (jq p (r32 SEX 1)) (jq i p))) 4)), true))

@[expose] noncomputable def c131001El (k : Nat) : Bool := slK 243 jEl (Nat.mul 16 k) 16

end CFSG.KD.E27J3S

end
