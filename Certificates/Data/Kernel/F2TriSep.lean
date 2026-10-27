module

public import Certificates.Data.Kernel.F2AlgRank

public section

namespace CFSG.KC.F2TriSep

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KC.F2AlgRank

@[expose] noncomputable def wordB (d A B : Nat) (w : List Bool) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun b _ ih acc => strictN (mulW d acc (Bool.rec (motive := fun _ => Nat) B A b)) ih) w

@[expose] noncomputable def outerK (d t f : Nat) : Nat :=
  orN d fun i => Nat.shiftLeft nIf(bit t i, f, nat_lit 0) (Nat.mul d i)

@[expose] noncomputable def colsK (d NT w k : Nat) : Bool :=
  allN d fun c => orB (Nat.blt c k)
    (strictB (rowF d NT c) fun x => orB (Nat.beq x (nat_lit 0)) (Nat.beq x w))

@[expose] noncomputable def triK (d : Nat) (G : List Nat) (tree : List (Nat × Nat))
    (masks ts : List Nat) (F Dm w : Nat) : Bool :=
  algK d G tree [idF d] fun L =>
    andB (allN (Nat.sub d (nat_lit 2)) fun k =>
        strictB (trK d (mulW d (Nat.xor (selK L (getL (nat_lit 0) masks k))
          (outerK d (getL (nat_lit 0) ts k) (rowF d F (Nat.succ k)))) Dm)) fun NT =>
        colsK d NT w (Nat.succ k))
      (andB (Nat.beq (mulW d Dm F) (idF d)) (Nat.beq (vmF d (trK d Dm) (pw2 (Nat.pred d))) w))

@[expose] noncomputable def vregK (d : Nat) (GT : List Nat) (tree : List (Nat × Nat))
    (acc : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun acc => k acc)
    (fun e _ ih acc => Prod.rec (motive := fun _ => Bool) (fun o g =>
      strictB (vmF d (getL (nat_lit 0) GT g) (getL (nat_lit 0) acc o)) fun v => ih (v :: acc)) e)
    tree acc

@[expose] noncomputable def packL (d : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor x (Nat.shiftLeft ih d)) L

@[expose] noncomputable def trL (d : Nat) (G : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun g _ ih => trK d g :: ih) G

@[expose] noncomputable def fixL (d : Nat) (G : List Nat) (w : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ ih => andB (Nat.beq (vmF d (trK d g) w) w) ih) G

@[expose] noncomputable def spinK (d : Nat) (G : List Nat) (tree : List (Nat × Nat))
    (v e Ri : Nat) : Bool :=
  andB (Nat.blt v (pw2 d)) (andB (Nat.blt e (pw2 d))
    (vregK d (trL d G) tree [v] fun L =>
      andB (Nat.beq (lenL L) (Nat.pred d)) (Nat.beq (mulW d (packL d (e :: L)) Ri) (idF d))))

end CFSG.KC.F2TriSep

end
