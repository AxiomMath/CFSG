module

public import Certificates.Data.Kernel.J4Q.Mat
public import Certificates.Data.Kernel.SporSch.J4S11
public import CFSG.Sporadic.GLQ.RegisterProgram

public section

namespace CFSG.KC.J4Sp

open CFSG.KC.J4Q CFSG.Sporadic.GLQ

abbrev Ent := Nat × Nat × Nat

@[expose] noncomputable def pullS (r : Nat) (L : List Ent)
    (k : Ent → List Ent → Option (List Ent)) : Option (List Ent) :=
  List.rec (motive := fun _ => (Ent → List Ent → Option (List Ent)) → Option (List Ent))
    (fun _ => none)
    (fun e t ih k => Bool.rec (motive := fun _ => Option (List Ent))
      (ih fun f L' => k f (List.cons e L')) (k e t) (Nat.beq e.1 r)) L k

@[expose] noncomputable def strictO (y : Nat) (k : Nat → Option (List Ent)) : Option (List Ent) :=
  Nat.rec (motive := fun _ => Option (List Ent)) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def pushS (n b0 r a b : Nat) (L : List Ent)
    (k : List Ent → Nat → Option (List Ent)) : Option (List Ent) :=
  Bool.rec (motive := fun _ => Option (List Ent)) none
    (strictO a fun x => strictO b fun y => k (List.cons (r, x, y) L) (Nat.succ r))
    (andB (Nat.ble b0 r) (Nat.blt r n))

@[expose] noncomputable def stepS (c rm one n : Nat) (ins : Instr) (L : List Ent) (b : Nat)
    (k : List Ent → Nat → Option (List Ent)) : Option (List Ent) :=
  Instr.rec (motive := fun _ => Option (List Ent))
    (fun i j r => pullS i L fun ei L1 => pullS j (List.cons ei L1) fun ej L2 =>
      pushS n b r (mulJ c rm ei.2.1 ej.2.1) (mulJ c rm ej.2.2 ei.2.2) (List.cons ej L2) k)
    (fun i r => pullS i L fun ei L1 => pushS n b r ei.2.2 ei.2.1 (List.cons ei L1) k)
    (fun e i r => pullS i L fun ei L1 =>
      pushS n b r (powJ c rm one ei.2.1 e) (powJ c rm one ei.2.2 e) (List.cons ei L1) k)
    ins

@[expose] noncomputable def runS (c rm one n : Nat) (prog : List Instr) (L : List Ent) (b : Nat) :
    Option (List Ent) :=
  List.rec (motive := fun _ => List Ent → Nat → Option (List Ent)) (fun L _ => some L)
    (fun ins _ ih L b => stepS c rm one n ins L b ih) prog L b

@[expose] noncomputable def getS (r : Nat) (L : List Ent) : Option (List Ent) :=
  pullS r L fun e _ => some (List.cons e List.nil)

@[expose] noncomputable def headB (B : Nat) (l : List Ent) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun e _ _ => Nat.beq e.2.1 B) l

@[expose] noncomputable def slpS (c rm one n K B : Nat) (prog : List Instr) (L : List Ent)
    (b : Nat) : Bool :=
  Option.rec (motive := fun _ => Bool) false
    (fun L' => Option.rec (motive := fun _ => Bool) false (headB B) (getS K L'))
    (runS c rm one n prog L b)

@[expose] noncomputable def slpT (c rm one n K B : Nat) (cs : List Char) (x1 x2 y1 y2 : Nat) :
    Bool :=
  Option.rec (motive := fun _ => Bool) false
    (fun codes => andB ((codes.map CFSG.KS.SporSch.J4E.decodeK).all (Instr.lt n))
      (slpS c rm one n K B (codes.map CFSG.KS.SporSch.J4E.decodeK) [(1, x1, x2), (2, y1, y2)] 3))
    (CFSG.KS.SporSch.J4E.parseK cs)

@[expose] noncomputable def mulQ (c rm : Nat) (p q : Nat × Nat) : Nat × Nat :=
  (mulJ c rm p.1 q.1, mulJ c rm q.2 p.2)

@[expose] noncomputable def letQ (one : Nat) (fs ss : List Nat) (l : Int) : Nat × Nat :=
  if 0 < l then (getN one fs (l.toNat - 1), getN one ss (l.toNat - 1))
  else (getN one ss ((-l).toNat - 1), getN one fs ((-l).toNat - 1))

@[expose] noncomputable def wordQ (c rm one : Nat) (fs ss : List Nat) (w : List Int) : Nat × Nat :=
  List.rec (motive := fun _ => Nat × Nat) (one, one)
    (fun l _ ih => mulQ c rm (letQ one fs ss l) ih) w

@[expose] noncomputable def etaQ (c rm one : Nat) (us : Nat → Nat × Nat) (n cc : Nat) : Nat × Nat :=
  (List.range n).foldl (fun acc j => if cc.testBit j then mulQ c rm acc (us j) else acc) (one, one)

end CFSG.KC.J4Sp

end
