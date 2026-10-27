module

public import Certificates.Data.Kernel.HexaK

public section

namespace CFSG.KC.HexaStabK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.HexaK
open CFSG.KLie.CT (anyN sumN andB orB notB pw2 bit)

@[expose] noncomputable def translK (w v : Nat) : Nat := pmk 64 w fun x => Nat.xor x v

@[expose] noncomputable def linVK (imgs : List Nat) (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun r ih acc => ih (Bool.rec (motive := fun _ => Nat) acc
      (Nat.xor acc (imgs.getD (Nat.sub (Nat.sub 6 r) 1) 0))
      (bit v (Nat.sub (Nat.sub 6 r) 1)))) 6 0

@[expose] noncomputable def linK (w : Nat) (imgs : List Nat) : Nat := pmk 64 w fun x => linVK imgs x

@[expose] noncomputable def presK (w : Nat) (oval : List (List Nat)) (t : Nat) : Bool :=
  oval.all fun L => oval.any fun L' => L.all fun x => L'.contains (pgC 64 w t x)

@[expose] noncomputable def memK (L : List Nat) (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => orB (Nat.beq a y) ih) L

@[expose] noncomputable def presL (oval : List (List Nat)) (imgs : List Nat) : Bool :=
  oval.all fun L => (fun T : List Nat => oval.any fun L' => T.all fun y => memK L' y)
    (L.map (linVK imgs))

@[expose] noncomputable def popK (k X : Nat) : Nat :=
  sumN k fun i => Bool.rec (motive := fun _ => Nat) 0 1 (bit X i)

@[expose] noncomputable def injK (w t : Nat) : Bool :=
  Nat.beq (popK (pw2 w) (Nat.rec (motive := fun _ => Nat) 0
    (fun x acc => Nat.lor acc (pw2 (pgC 64 w t x))) 64)) 64

@[expose] noncomputable def candImgs (p q r : Nat × Nat) : List Nat := [p.1, p.2, q.1, q.2, r.1, r.2]

@[expose] noncomputable def candOK (w : Nat) (oval : List (List Nat)) (NM : Nat)
    (TM : Nat → Nat) (W : List Nat) (c : Nat) (imgs : List Nat) : Bool :=
  orB (notB (andB (presL oval imgs) (strictB (linK w imgs) fun t => injK w t)))
    (strictB (linK w imgs) fun t =>
      strictB (Nat.mod (Nat.shiftRight (W.getD (Nat.div c 648) 0) (Nat.mul 12 (Nat.mod c 648)))
        4096) fun j => andB (Nat.blt j NM) (Nat.beq t (TM j)))

@[expose] noncomputable def stabBlockK (w : Nat) (oval : List (List Nat)) (P : List (Nat × Nat))
    (NM : Nat) (TM : Nat → Nat) (W : List Nat) (i : Nat) : Bool :=
  strictB P.length fun L =>
    (List.range L).all fun j => (List.range L).all fun k =>
      candOK w oval NM TM W (Nat.add (Nat.mul (Nat.add (Nat.mul i L) j) L) k)
        (candImgs (P.getD i (0, 0)) (P.getD j (0, 0)) (P.getD k (0, 0)))

@[expose] noncomputable def ovalOK (oval : List (List Nat)) : Bool :=
  oval.all fun L => L.all fun x => Nat.blt x 64

end CFSG.KC.HexaStabK

end
