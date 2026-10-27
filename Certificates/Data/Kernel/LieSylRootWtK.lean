module

public import Certificates.Data.LieSylRootWt
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace Certificates.Data.LieSylRootWtK

open CFSG.KC.Loop Certificates.Data.LieSylRootWt

@[expose] noncomputable def allK (f : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => Bool.and (f x) ih) l

@[expose] noncomputable def getK (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun m _ ih i => Nat.rec (motive := fun _ => Nat) m (fun j _ => ih j) i) l i

@[expose] noncomputable def getLK (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun m _ ih i => Nat.rec (motive := fun _ => List Nat) m (fun j _ => ih j) i) l i

@[expose] noncomputable def appK (l : List Nat) (x : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [x] (fun y _ ih => y :: ih) l

@[expose] noncomputable def strictBK (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def l0 (x : Nat) : Nat := Nat.mod x (nat_lit 65536)

@[expose] noncomputable def l1 (x : Nat) : Nat := Nat.mod (Nat.div x (nat_lit 65536)) (nat_lit 65536)

@[expose] noncomputable def l2 (x : Nat) : Nat :=
  Nat.mod (Nat.div x (nat_lit 4294967296)) (nat_lit 65536)

@[expose] noncomputable def l3 (x : Nat) : Nat :=
  Nat.mod (Nat.div x (nat_lit 281474976710656)) (nat_lit 65536)

@[expose] noncomputable def wK (bp : Nat) (cs : List Nat) : Nat :=
  Nat.add (Nat.add (Nat.mul (l0 bp) (getK cs (nat_lit 0))) (Nat.mul (l1 bp) (getK cs (nat_lit 1))))
    (Nat.add (Nat.mul (l2 bp) (getK cs (nat_lit 2))) (Nat.mul (l3 bp) (getK cs (nat_lit 3))))

@[expose] noncomputable def redP (w : Nat) : Nat :=
  Nat.add (Nat.add (Nat.mod (l0 w) (nat_lit 11)) (Nat.mul (nat_lit 65536) (Nat.mod (l1 w) (nat_lit 11))))
    (Nat.add (Nat.mul (nat_lit 4294967296) (Nat.mod (l2 w) (nat_lit 11)))
      (Nat.mul (nat_lit 281474976710656) (Nat.mod (l3 w) (nat_lit 11))))

@[expose] noncomputable def keyK (w : Nat) : Nat :=
  Nat.add (Nat.add (Nat.mod (l0 w) (nat_lit 11)) (Nat.mul (nat_lit 16) (Nat.mod (l1 w) (nat_lit 11))))
    (Nat.add (Nat.mul (nat_lit 256) (Nat.mod (l2 w) (nat_lit 11)))
      (Nat.mul (nat_lit 4096) (Nat.mod (l3 w) (nat_lit 11))))

@[expose] noncomputable def testK (mask bp : Nat) (cs : List Nat) : Bool :=
  strictBK (wK bp cs) fun w =>
    Nat.beq (Nat.land (Nat.shiftRight mask (keyK w)) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def stepK (cs : List Nat) (x : Nat) : Nat :=
  strictN (wK x cs) fun w => redP w

@[expose] noncomputable def itK (cs : List Nat) (n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ acc => strictN acc fun a => stepK cs a) n

@[expose] noncomputable def orderK (e : Nat) (cs : List Nat) : Bool :=
  Bool.and (Nat.beq (itK cs e (nat_lit 1)) (nat_lit 1))
    (Bool.and (Nat.beq (itK cs e (nat_lit 65536)) (nat_lit 65536))
      (Bool.and (Nat.beq (itK cs e (nat_lit 4294967296)) (nat_lit 4294967296))
        (Nat.beq (itK cs e (nat_lit 281474976710656)) (nat_lit 281474976710656))))

@[expose] noncomputable def searchK (RP : List Nat) (LP : List (List Nat)) (mask e : Nat) :
    Nat → Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → Bool)
    (fun _ cs => orderK e cs)
    (fun _ ih k cs => Bool.rec (motive := fun _ => Bool) (orderK e cs)
      (allK (fun g => Bool.or (Bool.not (allK (fun bp => testK mask bp (appK cs g)) (getLK LP k)))
        (ih (Nat.succ k) (appK cs g))) RP)
      (Nat.blt k (nat_lit 4)))

@[expose] def rI (v : List Int) (i : Nat) : Nat := ((v.getD i 0) % 11).toNat

@[expose] def pvI (v : List Int) : Nat :=
  rI v 0 + 65536 * rI v 1 + 4294967296 * rI v 2 + 281474976710656 * rI v 3

@[expose] def kvI (v : List Int) : Nat := rI v 0 + 16 * rI v 1 + 256 * rI v 2 + 4096 * rI v 3

@[expose] def maskOf (L : List Nat) : Nat := L.foldr (fun k m => m ||| (1 <<< k)) 0

@[expose] def levels4 (R : List (List Int)) : List (List (List Int)) :=
  (List.range 4).map fun k => R.filter fun b => level 4 b == k

end Certificates.Data.LieSylRootWtK

end
