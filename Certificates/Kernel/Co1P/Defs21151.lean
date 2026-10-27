module

public import Certificates.Kernel.Co1P.Defs21156
public import Certificates.Kernel.Co1P.Pin21151
public import Certificates.Data.Kernel.Co1PPath

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Patterson.Native

@[expose] noncomputable def GZ : List Nat := gensKz.map fun j => getL oneK GDS (j - 1)

@[expose] noncomputable def GZI : List Nat := gensKz.map fun j => getL oneK GDIS (j - 1)

@[expose] noncomputable def r4C (i : Nat) : Nat := tabK 32 PR4C i

@[expose] noncomputable def rF8 (i : Nat) : Nat := tabK 32 PRF8 i

@[expose] noncomputable def rF5 (i : Nat) : Nat := tabK 32 PRF5 i

@[expose] noncomputable def pt4C (i : Nat) : Nat × Bool := ptPK BK BIK r4C (repK 3) 10 i

@[expose] noncomputable def ptF8 (i : Nat) : Nat × Bool := ptPK GE GEI rF8 (repK 8) 10 i

@[expose] noncomputable def ptF5 (i : Nat) : Nat × Bool := ptPK GZ GZI rF5 (repK 5) 10 i

@[expose] noncomputable def sk4C (s : Nat) : Nat := tabK 64 SK4C s

@[expose] noncomputable def ix4C (s : Nat) : Nat := tabK 16 IX4C s

@[expose] noncomputable def skF8 (s : Nat) : Nat := tabK 64 SKF8 s

@[expose] noncomputable def ixF8 (s : Nat) : Nat := tabK 16 IXF8 s

@[expose] noncomputable def skF5 (s : Nat) : Nat := tabK 64 SKF5 s

@[expose] noncomputable def ixF5 (s : Nat) : Nat := tabK 16 IXF5 s

@[expose] noncomputable def mem4 (X : Nat) : Bool := memPin 34560 64 16 sk4C ix4C (fun i => (pt4C i).1) X

@[expose] noncomputable def key4C_chunk (c : Nat) : Bool := chunkK 34560 (keyAtP 34560 64 sk4C ix4C pt4C) c

@[expose] noncomputable def keyF8_chunk (c : Nat) : Bool := chunkK 24576 (keyAtP 24576 64 skF8 ixF8 ptF8) c

@[expose] noncomputable def keyF5_chunk (c : Nat) : Bool := chunkK 16384 (keyAtP 16384 64 skF5 ixF5 ptF5) c

@[expose] noncomputable def conjE (i b : Nat) : Nat :=
  mulWK (mulWK (mulWK (repXiK 1) (hisE i)) b) (mulWK (hsE i) (repXK 1))

@[expose] noncomputable def cntChunk (c : Nat) : Bool :=
  andB (Nat.beq (cntK 12600 (fun i => memE (conjE i (repK 4))) c) (getL 0 CN4 c))
    (Nat.beq (cntK 12600 (fun i => mem4 (conjE i (repK 8))) c) (getL 0 CN8 c))

@[expose] noncomputable def conjQ (i b : Nat) : Nat :=
  mulWK (mulWK (mulWK (repXiK 0) (hisW orbQMasks i)) b) (mulWK (hsW orbQMasks i) (repXK 0))

@[expose] noncomputable def sub45K : Bool :=
  (fun E Z A4a A4b A6 => andB (andB (andB (eqK (mulWK A4a A4a) E) (eqK (mulWK A4b A4b) E))
      (eqK (mulWK (mulWK A6 A6) A6) E))
    (andB (andB (memE (mulWK (mulWK (repXiK 1) (repK 4)) (repXK 1)))
      (andB (mem4 (mulWK (mulWK (repXiK 1) (repK 8)) (repXK 1)))
        (mem4 (mulWK (mulWK (repXiK 0) (repK 5)) (repXK 0)))))
    (andB (andB (invsOK GZ GZI) (Nat.beq (lenL GZ) 6))
      (GZ.all fun g => andB (eqK (mulWK g AL) (mulWK AL g)) (eqK (mulWK g Z) (mulWK Z g))))))
    (repK 1) (repK 0) (mulWK AL (repK 6)) (mulWK AL (repK 7)) (mulWK AL (repK 9))

end CertificateChecks.KernelCo1P

end
