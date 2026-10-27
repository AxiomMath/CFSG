module

public import Certificates.Kernel.Co1P.Chk21158
public import Certificates.Kernel.Co1P.PinEDefs
public import Certificates.Data.Kernel.Co1PLoop
public import Certificates.Data.Kernel.Co1BInner

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Patterson.Native

@[expose] noncomputable def bitsOf (ns : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun n _ ih => Nat.lor (Nat.shiftLeft 1 n) ih) ns

@[expose] noncomputable def xeP (k : Nat) : Nat := mulWK (hsE k) (repXK 1)

@[expose] noncomputable def xeiP (k : Nat) : Nat := mulWK (repXiK 1) (hisE k)

@[expose] noncomputable def adjP (X Xi B : Nat) : Bool := memE (mulWK (mulWK Xi B) X)

@[expose] noncomputable def treeK (ns ps : List Nat) (P : Nat → Bool) : Bool :=
  andB (andB (Nat.blt 0 (lenL ns)) (Nat.beq (lenL ps) (lenL ns)))
    (allN (lenL ns) fun r => (fun n => andB (andB (Nat.blt n 12600) (P n))
      (orB (Nat.beq r 0) (andB (Nat.blt (getL 0 ps r) r)
        (adjP (xeP n) (xeiP n) (ptPE (getL 0 ns (getL 0 ps r))))))) (getL 0 ns r))

@[expose] noncomputable def l2ns (t : Nat) : List Nat := (lvl2Data.getD t ([], [])).1

@[expose] noncomputable def l2ps (t : Nat) : List Nat := (lvl2Data.getD t ([], [])).2

@[expose] noncomputable def RB (t : Nat) : Nat := repK (d2Reps.getD t 0)

@[expose] noncomputable def RF (t : Nat) : Nat := repK (farReps.getD t 0)

@[expose] noncomputable def lvl2K (t : Nat) : Bool :=
  andB (andB (notB (eqK (RB t) AL)) (notB (memE (RB t))))
    (treeK (l2ns t) (l2ps t) fun n => adjP (xeP n) (xeiP n) (RB t))

@[expose] noncomputable def farK (t : Nat) : Bool :=
  (fun c m => andB (andB (notB (eqK (RF t) AL)) (notB (memE (RF t))))
    (andB (andB (Nat.blt c 12600) (Nat.blt m 12600))
      (adjP (mulWK (xeP c) (xeP m)) (mulWK (xeiP m) (xeiP c)) (RF t))))
    (farPath.getD t (0, 0)).1 (farPath.getD t (0, 0)).2

@[expose] noncomputable def aeK : Bool :=
  andB (eqK (mulWK (mulWK (getL oneK GDS 189) AL) (getL oneK GDIS 189)) (mulWK AL (repK 1)))
    (notB (memQ (mulWK (mulWK (repXiK 1) AL) (repXK 1))))

@[expose] noncomputable def ronanAtW (M : Nat → Nat) (k : Nat) : Bool :=
  strictB (xeP k) fun X => strictB (xeiP k) fun Xi =>
    andB (allN 7 fun t => orB (notB (adjP X Xi (RB t))) (bit (M t) k))
      (allN 2 fun t => notB (adjP X Xi (RF t)))

@[expose] noncomputable def maskL2 (t : Nat) : Nat := bitsOf (l2ns t)

@[expose] noncomputable def ronanChunk (c : Nat) : Bool :=
  strictB (maskL2 0) fun m0 => strictB (maskL2 1) fun m1 => strictB (maskL2 2) fun m2 =>
  strictB (maskL2 3) fun m3 => strictB (maskL2 4) fun m4 => strictB (maskL2 5) fun m5 =>
  strictB (maskL2 6) fun m6 =>
    chunkK 12600 (ronanAtW fun t => getL 0 [m0, m1, m2, m3, m4, m5, m6] t) c

end CertificateChecks.KernelCo1P

end
