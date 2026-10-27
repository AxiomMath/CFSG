module

public import Certificates.Data.Kernel.J4M4F.Defs
public import Certificates.Data.Kernel.J4Q.QT

public section

namespace CFSG.KD.J4M4Card

open CFSG.KC.J4Q CFSG.KD.J4M4F

@[expose] noncomputable def getLL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun m _ ih i => Nat.rec (motive := fun _ => List Nat) m (fun j _ => ih j) i) l i

@[expose] noncomputable def conjW (c rm one G Gi : Nat) (M Mi : List Nat) (w : List Int) : Nat :=
  mulJ c rm (mulJ c rm G (wordJ c rm one M Mi w)) Gi

@[expose] noncomputable def masksAt (c rm one : Nat) (Us : List Nat) (H Hi : Nat) (ms : List Nat) :
    Bool :=
  strictB H fun h => strictB Hi fun hi => allR 11 fun k =>
    Nat.beq (mulJ c rm (mulJ c rm h (etaK c rm one Us (Nat.shiftLeft 1 k))) hi)
      (etaK c rm one Us (getN 0 ms k))

@[expose] noncomputable def masksK (c rm one G Gi : Nat) (M Mi Us : List Nat) (W Wi : Nat → List Int)
    (T : List (List Nat)) (lo n : Nat) : Bool :=
  allR n fun t => masksAt c rm one Us (conjW c rm one G Gi M Mi (W (Nat.add lo t)))
    (conjW c rm one G Gi M Mi (Wi (Nat.add lo t))) (getLL T (Nat.add lo t))

@[expose] noncomputable def witChk (c rm one G Gi : Nat) (Us FM : List Nat) (k j lo n : Nat) : Bool :=
  strictB (mulJ c rm (mulJ c rm Gi (etaK c rm one Us (Nat.shiftLeft 1 k))) G) fun e =>
    strictB (mulJ c rm (mulJ c rm e (getN one FM j)) e) fun x =>
      allR n fun t => neN x (fRK c rm one FM (Nat.add lo t))

@[expose] noncomputable def keK (c rm one G Gi : Nat) (M Mi Us : List Nat) :
    List (List Int) → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun w _ ih ms => List.rec (motive := fun _ => Bool) false
      (fun m ms' _ => andB (Nat.beq (wordJ c rm one M Mi w)
        (mulJ c rm (mulJ c rm Gi (etaK c rm one Us m)) G)) (ih ms')) ms)

end CFSG.KD.J4M4Card

end
