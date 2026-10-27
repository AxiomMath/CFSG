module

public import Certificates.Kernel.Co1P.Pin21150
public import Certificates.Kernel.Co1P.Pin21150H
public import Certificates.Data.Kernel.Co1PPathM
public import Certificates.Data.Kernel.Co1BInner
public import Certificates.Kernel.Co1P.Defs21156

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Patterson.Native

@[expose] noncomputable def brI (l X : Nat) : Nat := mulWK (mulWK (getL 0 BK l) X) (getL 0 BIK l)

@[expose] noncomputable def inE (Y j : Nat) : Bool := andB (Nat.blt j 12600) (eqK Y (ptPE j))

@[expose] noncomputable def closE (E k : Nat) : Bool :=
  strictB (ptPE k) fun P => allN 8 fun l => strictB (brI l P) fun Y =>
    inE Y (fget E (Nat.add (Nat.mul 8 (Nat.mod k 64)) l) 16)

@[expose] noncomputable def closEC (c : Nat) : Bool := strictB (getL 0 JE c) fun E => chunkK 12600 (closE E) c

@[expose] noncomputable def th4 (i : Nat) : Nat := tabK 576 HS4C i

@[expose] noncomputable def thi4 (i : Nat) : Nat := tabK 576 HIS4C i

@[expose] noncomputable def r4W (i : Nat) : Nat := fget (getL 0 R4W (Nat.div i 1024)) (Nat.mod i 1024) 32

@[expose] noncomputable def pt4M (i : Nat) : Nat × Bool := ptM BK BIK th4 thi4 2692 r4W (repK 3) 4 i

@[expose] noncomputable def th4_chunk (c : Nat) : Bool :=
  andB (pinChunk (hsAct BK) oneK th4 r4W 2692 c) (pinChunk (hisAct BIK) oneK thi4 r4W 2692 c)

@[expose] noncomputable def in4 (Y j : Nat) : Bool :=
  andB (Nat.blt j 34560) ((fun p => andB p.2 (eqK Y p.1)) (pt4M j))

@[expose] noncomputable def clos4 (E i : Nat) : Bool :=
  (fun p => andB p.2 (strictB p.1 fun P => allN 8 fun l => strictB (brI l P) fun Y =>
    in4 Y (fget E (Nat.add (Nat.mul 8 (Nat.mod i 64)) l) 16))) (pt4M i)

@[expose] noncomputable def clos4C (c : Nat) : Bool := strictB (getL 0 J4 c) fun E => chunkK 34560 (clos4 E) c

@[expose] noncomputable def clos4Q (q c : Nat) : Bool := clos4C (Nat.add (Nat.mul 135 q) c)

@[expose] noncomputable def clos4Q0 (c : Nat) : Bool := clos4Q 0 c
@[expose] noncomputable def clos4Q1 (c : Nat) : Bool := clos4Q 1 c
@[expose] noncomputable def clos4Q2 (c : Nat) : Bool := clos4Q 2 c
@[expose] noncomputable def clos4Q3 (c : Nat) : Bool := clos4Q 3 c

@[expose] noncomputable def rA4 (i : Nat) : Nat := fget (getL 0 RA4W (Nat.div i 1024)) (Nat.mod i 1024) 32

@[expose] noncomputable def ptA4 (i : Nat) : Nat × Bool := ptPK BK BIK rA4 (repK 2) 10 i

@[expose] noncomputable def skA4 (s : Nat) : Nat := tabK 64 SKA4 s

@[expose] noncomputable def ixA4 (s : Nat) : Nat := tabK 16 IXA4 s

@[expose] noncomputable def pfK (w : Nat) (C : List Nat) (c E s : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (tabK w C s) (fget E (Nat.mod s 64) w) (Nat.beq (Nat.div s 64) c)

@[expose] noncomputable def keyA4_chunk (c : Nat) : Bool :=
  strictB (getL 0 SKA4 c) fun E1 => strictB (getL 0 IXA4 c) fun E2 =>
    chunkK 60480 (keyAtP 60480 64 (pfK 64 SKA4 c E1) (pfK 16 IXA4 c E2) ptA4) c

@[expose] noncomputable def ptsQ : List Nat := ptsL BK BIK 8 (repK 0) (recsT orbQMasks)

@[expose] noncomputable def closQ : Bool :=
  andB (orbChk BK BIK 8 (repK 0) 9 (recsT orbQMasks))
    ((fun S => andB (andB (sincK S) (treeAll 9 S))
      ((fun T => ptsQ.all fun P => allN 8 fun l => memKT (keyK (brI l P)) T) (treeOf 9 S)))
      (sortP 9 (modL ptsQ)))

end CertificateChecks.KernelCo1P

end
