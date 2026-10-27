module

public import Certificates.Data.Kernel.SporSch.Co1Mat
public import Certificates.Data.Kernel.Spor.Co2Shape
public import Certificates.Data.Kernel.Spor.Mathieu

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2Shape CFSG.KS.Mathieu

@[expose] noncomputable def powK (X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idM (fun _ ih => strictN ih (fun Y => mulK Y X)) e

@[expose] noncomputable def dig3 (n i : Nat) : Nat :=
  Nat.mod (Nat.div n (Nat.pow (nat_lit 3) i)) (nat_lit 3)

@[expose] noncomputable def eProdK (A : Nat → Nat) (n : Nat) : Nat :=
  foldN (nat_lit 6) (fun i acc => mulK (powK (A i) (dig3 n i)) acc) idM

@[expose] noncomputable def idxK (MsP k : Nat) : Nat := fld(MsP, Nat.mul (nat_lit 10) k, nat_lit 1023)

@[expose] noncomputable def distP (MsP n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun k ih M => strictB (idxK MsP k) (fun x => bAnd(Nat.blt x (nat_lit 729),
      bAnd(bIf(hasBit M x, false, true), strictB (Nat.lor M (Nat.shiftLeft (nat_lit 1) x)) ih))))
    n

@[expose] noncomputable def incSl (A : Nat → Nat) (MsP lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun k => bIf(Nat.blt (Nat.succ k) (nat_lit 729),
    Nat.blt (eProdK A (idxK MsP k)) (eProdK A (idxK MsP (Nat.succ k))), true)))

@[expose] noncomputable def eK (A : Nat → Nat) (MsP : Nat) : Bool :=
  bAnd(distP MsP (nat_lit 729) (nat_lit 0),
    allN (nat_lit 6) (fun i => Nat.beq (eProdK A (Nat.pow (nat_lit 3) i)) (A i)))

@[expose] noncomputable def elemK (A : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 6) (fun i => allN (nat_lit 6) (fun j =>
      Nat.beq (mulK (A i) (A j)) (mulK (A j) (A i)))),
    allN (nat_lit 6) (fun i => Nat.beq (powK (A i) (nat_lit 3)) idM))

@[expose] noncomputable def ngetL (l : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) l

@[expose] noncomputable def f4LoK (cs : List Nat) : Nat :=
  foldN (nat_lit 12) (fun k s => nIf(Nat.beq (Nat.mod (nget cs k) (nat_lit 2)) (nat_lit 1),
    Nat.xor s (Nat.shiftLeft (nat_lit 1) k), s)) (nat_lit 0)

@[expose] noncomputable def f4HiK (PZ : Nat) (cs : List Nat) : Nat :=
  foldN (nat_lit 12) (fun k s =>
    nIf(Nat.beq (Nat.mod (Nat.div (nget cs k) (nat_lit 2)) (nat_lit 2)) (nat_lit 1),
      Nat.xor s (actK PZ (Nat.shiftLeft (nat_lit 1) k)), s)) (nat_lit 0)

@[expose] noncomputable def qK (PZ : Nat) (fv : List (List Nat)) (j : Nat) : Nat :=
  Nat.xor (f4LoK (ngetL fv j)) (f4HiK PZ (ngetL fv j))

@[expose] noncomputable def zPowK (PZ e v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) v (fun _ ih => strictN ih (fun u => actK PZ u)) e

@[expose] noncomputable def colK (PZ : Nat) (fv : List (List Nat)) (k : Nat) : Nat :=
  strictN (qK PZ fv (Nat.shiftRight k (nat_lit 1))) (fun q =>
    nIf(Nat.beq (Nat.land k (nat_lit 1)) (nat_lit 0), q, actK PZ q))

@[expose] noncomputable def transOK (PZ PQ : Nat) (fv : List (List Nat)) : Bool :=
  strictB (foldN (nat_lit 24) (fun k s => Nat.lor s
      (Nat.shiftLeft (colK PZ fv k) (Nat.mul (nat_lit 24) k))) (nat_lit 0)) (fun C =>
    allN (nat_lit 24) (fun i => Nat.beq (rowK PQ i)
      (foldN (nat_lit 24) (fun k s => Nat.lor s
        (Nat.shiftLeft (Nat.land (Nat.shiftRight (rowK C k) i) (nat_lit 1)) k)) (nat_lit 0))))

@[expose] noncomputable def eigenK (A : Nat → Nat) (PZ PQ PQI : Nat) (fv ec : List (List Nat)) :
    Bool :=
  bAnd(allN (nat_lit 6) (fun i => allN (nat_lit 12) (fun j => strictB (qK PZ fv j) (fun q =>
    strictB (nget (ngetL ec j) i) (fun g =>
      bAnd(Nat.blt g (nat_lit 3), Nat.beq (actK (A i) q) (zPowK PZ g q)))))),
  bAnd(Nat.beq (mulK PZ PZ) (Nat.xor PZ idM),
  bAnd(transOK PZ PQ fv,
  bAnd(invOKK PQ PQI, bAnd(invOKK PQI PQ, Nat.beq (A (nat_lit 0)) PZ)))))

end CFSG.KS.SporSch.M24

end
