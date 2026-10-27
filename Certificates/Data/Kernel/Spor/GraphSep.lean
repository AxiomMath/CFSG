module

public import Certificates.Data.Kernel.Spor.RawTree

public section

namespace CFSG.KS.GraphSep

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def listK (n w m d : Nat) (NB AL : Nat → Nat) (v : Nat) : Bool :=
  strictB (AL v) (fun A => bAnd(allN d (fun i => Nat.blt (pg w m A i) n),
    Nat.beq (NB v) (foldUp d (fun i acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (pg w m A i)))
      (nat_lit 0))))

@[expose] noncomputable def invK (w m d : Nat) (NB AL : Nat → Nat) (s v : Nat) : Bool :=
  strictB (AL v) (fun A => strictB (NB (pg w m s v)) (fun N =>
    allN d (fun i => hasBit N (pg w m s (pg w m A i)))))

@[expose] noncomputable def ordK (n w m nb BP ORD : Nat) : Bool :=
  bAnd(Nat.ble nb n, bAnd(allN nb (fun t => Nat.beq (pg w m ORD t) (pg w m BP t)),
    Nat.beq (foldUp n (fun k acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (pg w m ORD k)))
      (nat_lit 0)) (mask n)))

@[expose] noncomputable def fixedK (w m ORD k : Nat) : Nat :=
  foldUp k (fun i acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (pg w m ORD i))) (nat_lit 0)

@[expose] noncomputable def wEnt (w R i : Nat) : Nat :=
  pg (Nat.succ w) (mask (Nat.succ w)) (Nat.shiftRight R (nat_lit 8)) i

@[expose] noncomputable def nbBit (w m : Nat) (NB : Nat → Nat) (ORD p x : Nat) : Nat :=
  Nat.land (Nat.shiftRight (NB (pg w m ORD p)) x) (nat_lit 1)

@[expose] noncomputable def wSet (n w m : Nat) (NB : Nat → Nat) (ORD e : Nat) : Nat :=
  strictN (NB (pg w m ORD (Nat.shiftRight e (nat_lit 1)))) (fun N =>
    nIf(Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1), N, Nat.xor (mask n) N))

@[expose] noncomputable def refK (n w m : Nat) (NB WT : Nat → Nat) (ORD k : Nat) : Bool :=
  strictB (pg w m ORD k) (fun x => strictB (WT k) (fun R =>
  strictB (Nat.land R (nat_lit 255)) (fun c =>
  bAnd(allN c (fun i => strictB (wEnt w R i) (fun e =>
      bAnd(Nat.blt (Nat.shiftRight e (nat_lit 1)) k,
        Nat.beq (Nat.land e (nat_lit 1)) (nbBit w m NB ORD (Nat.shiftRight e (nat_lit 1)) x)))),
    Nat.beq (foldUp c (fun i acc => Nat.land acc (wSet n w m NB ORD (wEnt w R i)))
        (Nat.xor (mask n) (fixedK w m ORD k)))
      (Nat.shiftLeft (nat_lit 1) x)))))

@[expose] noncomputable def listSl (n w m d : Nat) (NB AL : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun i => bIf(Nat.blt (Nat.add lo i) n, listK n w m d NB AL (Nat.add lo i), true))

@[expose] noncomputable def invSl (n w m d : Nat) (NB AL PS : Nat → Nat) (j lo len : Nat) : Bool :=
  strictB (PS j) (fun s => allN len (fun i =>
    bIf(Nat.blt (Nat.add lo i) n, invK w m d NB AL s (Nat.add lo i), true)))

@[expose] noncomputable def refSl (n w m nb : Nat) (NB WT : Nat → Nat) (ORD lo len : Nat) : Bool :=
  allN len (fun i => bIf(Nat.blt (Nat.add lo i) n, bIf(Nat.blt (Nat.add lo i) nb, true,
    refK n w m NB WT ORD (Nat.add lo i)), true))

end CFSG.KS.GraphSep

end
