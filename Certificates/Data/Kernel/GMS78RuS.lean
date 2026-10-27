module

public import Certificates.Data.Kernel.GMS78RuNE

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def sGamRow (GT : List (List Nat)) (c : Nat) : Nat :=
  neGet 0 (neGet [] GT (Nat.shiftRight c 4)) (Nat.land c 15)

@[expose] noncomputable def sMulK (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO x y : Nat) :
    Nat :=
  (fun pc pt pd qc qt qd => (fun dp => (fun dc dt => Nat.lor (Nat.xor pc dc) (Nat.lor
      (Nat.shiftLeft (Nat.xor (Nat.xor (Nat.xor (Nat.xor pt (fget LIN (Nat.add (Nat.mul 8 pd) qt) 3))
        dt) (fget (sGamRow GT pc) dc 3)) (fget DO (Nat.add (Nat.mul 8 pd) qd) 1)) 8)
      (Nat.shiftLeft (fget DM (Nat.add (Nat.mul 8 pd) qd) 3) 11)))
    (Nat.land dp 255) (Nat.shiftRight dp 8)) (fget (neGet 0 DPR pd) qc 11))
  (Nat.land x 255) (Nat.land (Nat.shiftRight x 8) 7) (Nat.land (Nat.shiftRight x 11) 7)
  (Nat.land y 255) (Nat.land (Nat.shiftRight y 8) 7) (Nat.land (Nat.shiftRight y 11) 7)

@[expose] noncomputable def sLift16 (p : Nat) : Nat :=
  Nat.lor (Nat.land p 255) (Nat.lor (Nat.shiftLeft (Nat.mul 4 (Nat.land (Nat.shiftRight p 8) 1)) 8)
    (Nat.shiftLeft (fget (nat_lit 3864) (Nat.shiftRight p 9) 3) 11))

@[expose] noncomputable def sEnc16 (x : Nat) : Nat :=
  Nat.add (Nat.land x 255) (Nat.add (Nat.mul 256 (Nat.land (Nat.shiftRight x 10) 1))
    (Nat.mul 512 (Nat.shiftRight x 12)))

@[expose] noncomputable def mul16K (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO p q : Nat) :
    Nat :=
  sEnc16 (sMulK GT DPR LIN DM DO (sLift16 p) (sLift16 q))

@[expose] noncomputable def sLift17 (p : Nat) : Nat :=
  Nat.lor (Nat.land p 255) (Nat.lor (Nat.shiftLeft (Nat.mul 2 (Nat.land (Nat.shiftRight p 8) 3)) 8)
    (Nat.shiftLeft (Nat.land (Nat.shiftRight p 10) 7) 11))

@[expose] noncomputable def sEnc17 (x : Nat) : Nat :=
  Nat.add (Nat.land x 255) (Nat.add (Nat.mul 256 (Nat.land (Nat.shiftRight x 9) 3))
    (Nat.mul 1024 (Nat.land (Nat.shiftRight x 11) 7)))

@[expose] noncomputable def mul17K (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO p q : Nat) :
    Nat :=
  sEnc17 (sMulK GT DPR LIN DM DO (sLift17 p) (sLift17 q))

@[expose] noncomputable def sFilter (n : Nat) (p : Nat → Bool) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun i ih acc => ih (Bool.rec (motive := fun _ => List Nat) acc (List.cons i acc) (p i))) n []

@[expose] noncomputable def sKey (m : Nat → Nat → Nat) (n u : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun p acc => strictN acc fun a =>
    Bool.rec (motive := fun _ => Nat) a
      ((fun s => Nat.add a (Nat.add 1 (Nat.add
        (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq s u)) 14)
        (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq s 256)) 28)))) (m p p))
      (Nat.beq (m p u) (m u p))) n

@[expose] noncomputable def kN (k : Nat) : Nat := Nat.land k 16383
@[expose] noncomputable def kR1 (k : Nat) : Nat := Nat.land (Nat.shiftRight k 14) 16383
@[expose] noncomputable def kR2 (k : Nat) : Nat := Nat.land (Nat.shiftRight k 28) 16383

@[expose] noncomputable def sZipAll (g : Nat → Nat → Bool) (U K : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun u _ ih K => andB (g u (neGet 0 K 0))
      (ih (List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) K))) U K

@[expose] noncomputable def sAllPairs (f : Nat → Nat → Nat → Nat → Bool) (U K : List Nat) : Bool :=
  sZipAll (fun u k => sZipAll (fun v l => f u k v l) U K) U K

@[expose] noncomputable def kKeyPart (k : Nat) : Nat := Nat.land k (Nat.sub (pw2 42) 1)

@[expose] noncomputable def sInvs (m : Nat → Nat → Nat) (n : Nat) : List Nat :=
  sFilter n fun u => andB (Nat.beq (m u u) 0) (andB (notB (Nat.beq u 0)) (notB (Nat.beq u 256)))

@[expose] noncomputable def kWp (k : Nat) : Nat := fget (Nat.shiftRight k 42) 0 11
@[expose] noncomputable def kWw (k : Nat) : Nat := fget (Nat.shiftRight k 42) 1 11

@[expose] noncomputable def kFin16 (m : Nat → Nat → Nat) (INVL KEYL : List Nat) : Bool :=
  andB (Nat.beq (neLen KEYL) (neLen INVL)) <|
  andB (sAllPairs (fun _ ka _ kb => orB (notB (andB (Nat.beq (kN ka) (kN kb))
      (andB (Nat.beq (kR1 ka) (kR2 kb)) (Nat.beq (kR2 ka) (kR1 kb))))) (Nat.beq (kN ka) 128))
    INVL KEYL) <|
  andB (sZipAll (fun u k => orB (notB (Nat.beq (kN k) 128)) ((fun p w => (fun pp =>
      andB (Nat.blt p 2048) (andB (Nat.blt w 2048) (andB (Nat.beq (m p u) (m u p))
        (andB (notB (Nat.beq pp 0)) (Nat.beq (m w u) (m (m u pp) w)))))) (m p p)) (kWp k) (kWw k)))
    INVL KEYL) <|
  andB (allN (nat_lit 2048) fun p => Nat.beq (Nat.shiftRight (m 256 (m p p)) 9) 0) <|
  andB (sZipAll (fun u k => orB (notB (Nat.beq (Nat.shiftRight u 9) 0)) (notB (Nat.beq (kN k) 128)))
    INVL KEYL) <|
  allN (nat_lit 2048) fun p => Nat.beq (m p 256) (m 256 p)

@[expose] noncomputable def kZ1 (k : Nat) : Nat := fget (Nat.shiftRight k 42) 0 9
@[expose] noncomputable def kZ2 (k : Nat) : Nat := fget (Nat.shiftRight k 42) 1 9

@[expose] noncomputable def kNeedZ (u k : Nat) : Bool :=
  andB (notB (Nat.beq (Nat.shiftRight u 10) 0))
    (andB (Nat.beq (kN k) 256) (Nat.beq (kR1 k) (kR2 k)))

@[expose] noncomputable def czPack8 (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s 8))) l 0

@[expose] noncomputable def sZx (m : Nat → Nat → Nat) (C : List Nat) (u : Nat) : Nat :=
  (fun IDX => (fun rows => (fun iu i2 =>
      Nat.rec (motive := fun _ => Nat) 0 (fun i acc => strictN acc fun a =>
        (fun Ri => (fun f1 f2 => Nat.add a (Nat.add (Bool.rec (motive := fun _ => Nat) 0 1 f1)
            (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 f2) 9)))
          (allN (nat_lit 256) fun j => (fun pq qp => orB (Nat.beq pq qp)
              (Nat.beq pq (fget (neGet 0 rows iu) qp 8))) (fget Ri j 8) (fget (neGet 0 rows j) i 8))
          (allN (nat_lit 256) fun j => (fun pq qp => orB (Nat.beq pq qp)
              (Nat.beq pq (fget (neGet 0 rows i2) qp 8))) (fget Ri j 8) (fget (neGet 0 rows j) i 8)))
        (neGet 0 rows i)) (nat_lit 256))
      (Nat.sub (fget IDX u 9) 1) (Nat.sub (fget IDX 256 9) 1))
    (List.rec (motive := fun _ => List Nat) []
      (fun p _ ih => List.cons (czPack8 (List.rec (motive := fun _ => List Nat) []
        (fun q _ ih2 => List.cons (Nat.sub (fget IDX (m p q) 9) 1) ih2) C)) ih) C))
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.lor (Nat.shiftLeft (Nat.succ i) (Nat.mul 9 x)) (ih (Nat.succ i))) C 0)

@[expose] noncomputable def kKey17 (m : Nat → Nat → Nat) (u k : Nat) : Bool :=
  andB (Nat.beq (sKey m 8192 u) (kKeyPart k))
    (Bool.rec (motive := fun _ => Bool) (Nat.beq (Nat.shiftRight k 42) 0)
      (andB (Nat.beq (neLen (sFilter 8192 fun p => Nat.beq (m p u) (m u p))) 256)
        (Nat.beq (sZx m (sFilter 8192 fun p => Nat.beq (m p u) (m u p)) u) (Nat.shiftRight k 42)))
      (kNeedZ u k))

@[expose] noncomputable def kFin17 (m : Nat → Nat → Nat) (inX : Nat → Bool) (INVL KEYL : List Nat) :
    Bool :=
  andB (Nat.beq (neLen KEYL) (neLen INVL)) <|
  andB (allN (nat_lit 8192) fun p => Nat.beq (m p 256) (m 256 p)) <|
  sAllPairs (fun u ka v kb => orB (inX u) <| orB (notB (andB (Nat.beq (kN ka) (kN kb))
      (andB (Nat.beq (kR1 ka) (kR2 kb)) (Nat.beq (kR2 ka) (kR1 kb))))) <|
    orB (andB (Nat.beq (kN ka) 128) (orB (Nat.beq (Nat.shiftRight u 10) 1)
      (Nat.beq (Nat.shiftRight u 10) 5))) <|
    andB (kNeedZ u ka) (andB (kNeedZ v kb)
      (orB (notB (Nat.beq (kZ1 ka) (kZ2 kb))) (notB (Nat.beq (kZ2 ka) (kZ1 kb))))))
    INVL KEYL

end CFSG.KC.GMS

end
