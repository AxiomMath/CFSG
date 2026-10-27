module

public section

namespace CFSG.TcRes.TK

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def fld (t w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight t (Nat.mul w i)) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def ones (k : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) k)) (nat_lit 1)) (nat_lit 65535)

@[expose] noncomputable def dP (n pr : Nat) : Nat :=
  Nat.add (fld pr (nat_lit 16) (Nat.sub n (nat_lit 1)))
    (fld pr (nat_lit 16) (Nat.sub (Nat.mul (nat_lit 3) n) (nat_lit 1)))

@[expose] noncomputable def dQ (n pr : Nat) : Nat :=
  fld pr (nat_lit 16) (Nat.sub (Nat.mul (nat_lit 2) n) (nat_lit 1))

@[expose] noncomputable def allLt (c : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun m ih => andB (p m) ih) c

@[expose] noncomputable def cRowOK (n : Nat) (yc : Nat → Nat) (xi yi m : Nat) : Bool :=
  strictB (Nat.mul xi (yc m)) fun pr =>
    Nat.beq (Nat.add (fld yi (nat_lit 16) (Nat.sub (Nat.sub n (nat_lit 1)) m)) (dQ n pr))
      (Nat.add (fld yi (nat_lit 16) (Nat.sub (Nat.sub (Nat.mul (nat_lit 2) n) (nat_lit 1)) m))
        (dP n pr))

@[expose] noncomputable def parOK (n W : Nat) (rt : Nat → Nat) (PAR i : Nat) : Bool :=
  strictB (fld PAR (nat_lit 16) i) fun e =>
    strictB (Nat.land e (nat_lit 255)) fun p =>
      strictB (Nat.shiftRight e (nat_lit 8)) fun k =>
        andB (Nat.blt p i) (andB (Nat.blt k n) (Nat.beq (fld (rt k) W p) i))

@[expose] noncomputable def rootOK (n N W : Nat) (yc rt : Nat → Nat) (V X Y NEG PAR i : Nat) :
    Bool :=
  strictB (Nat.mul (nat_lit 16) n) fun K =>
  strictB (ones n) fun O =>
  strictB (ones (Nat.mul (nat_lit 2) n)) fun O2 =>
  strictB (fld V K i) fun vi =>
  strictB (fld X (Nat.mul (nat_lit 2) K) i) fun xi =>
  strictB (fld Y (Nat.mul (nat_lit 2) K) i) fun yi =>
  strictB (fld NEG W i) fun j =>
    andB (Nat.beq (Nat.land vi (Nat.mul (nat_lit 65520) O)) (nat_lit 0))
    (andB (Nat.beq (Nat.land xi (Nat.mul (nat_lit 65528) O2)) (nat_lit 0))
    (andB (Nat.beq (Nat.land yi (Nat.mul (nat_lit 65532) O2)) (nat_lit 0))
    (andB (Nat.beq (Nat.add vi (Nat.shiftRight xi K))
        (Nat.add (fld xi K (nat_lit 0)) (Nat.mul (nat_lit 7) O)))
    (andB (allLt n (cRowOK n yc xi yi))
    (andB (andB (Nat.blt j N) (Nat.beq (Nat.add (fld V K j) vi) (Nat.mul (nat_lit 14) O)))
      (Bool.rec (motive := fun _ => Bool) (parOK n W rt PAR i)
        (Nat.beq vi (Nat.add (Nat.mul (nat_lit 7) O) (Nat.shiftLeft (nat_lit 1)
          (Nat.mul (nat_lit 16) i))))
        (Nat.blt i n)))))))

@[expose] noncomputable def entryOK (n N W K O : Nat) (V X r vg yg ag v : Nat) : Bool :=
  strictB (fld r W v) fun t =>
  strictB (Nat.mul (fld X (Nat.mul (nat_lit 2) K) v) yg) fun pr =>
  strictB (dP n pr) fun p =>
  strictB (dQ n pr) fun q =>
    andB (Nat.blt t N)
    (andB (Nat.beq
        (Nat.add (Nat.add (fld V K t) (Nat.mul p vg)) (Nat.mul (Nat.mul (nat_lit 7) q) O))
        (Nat.add (Nat.add (fld V K v) (Nat.mul q vg)) (Nat.mul (Nat.mul (nat_lit 7) p) O)))
      (Nat.beq (fld ag (nat_lit 1) v)
        (Bool.rec (motive := fun _ => Nat) (nat_lit 1) (nat_lit 0) (Nat.beq p q))))

@[expose] noncomputable def rowOK (n N W : Nat) (rt : Nat → Nat) (V X Y ADJ g : Nat) : Bool :=
  strictB (Nat.mul (nat_lit 16) n) fun K =>
  strictB (ones n) fun O =>
  strictB (rt g) fun r =>
  strictB (fld V K g) fun vg =>
  strictB (fld Y (Nat.mul (nat_lit 2) K) g) fun yg =>
  strictB (fld ADJ N g) fun ag =>
    allLt N (entryOK n N W K O V X r vg yg ag)

@[expose] noncomputable def srtWalk (N W K V SRT : Nat) (c : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih s prev =>
      strictB (fld SRT W s) fun i =>
      strictB (fld V K i) fun key =>
        andB (andB (Nat.blt i N) (Nat.blt prev key))
          (strictB (Nat.add s (nat_lit 1)) fun s' => ih s' key)) c

@[expose] noncomputable def srtOK (n N W : Nat) (yc : Nat → Nat) (V SRT : Nat) : Bool :=
  strictB (ones (Nat.mul (nat_lit 2) n)) fun O2 =>
    andB (allLt n fun m => Nat.beq (Nat.land (yc m) (Nat.mul (nat_lit 65532) O2)) (nat_lit 0))
      (srtWalk N W (Nat.mul (nat_lit 16) n) V SRT N (nat_lit 0) (nat_lit 0))

end CFSG.TcRes.TK

end
