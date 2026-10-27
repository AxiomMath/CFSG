module

public import Certificates.Data.Kernel.F4Mat

public section

namespace CFSG.KC.S23

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def rowG (M t : Nat) : Nat := fget M t (nat_lit 22)

@[expose] noncomputable def act (M v : Nat) : Nat :=
  xorN (nat_lit 22) fun i => nIf(bit v i, rowG M i, nat_lit 0)

@[expose] noncomputable def mat (N6 k : Nat) : Nat := fget N6 k (nat_lit 484)

@[expose] noncomputable def wact (N6 : Nat) (w : List Nat) (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun k _ ih c => strictN (act (mat N6 k) c) ih) w c

@[expose] noncomputable def delta (w : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun k _ ih => Bool.rec (motive := fun _ => List Nat) (List.cons k ih)
      (List.cons (nat_lit 2) (List.cons (nat_lit 1) (List.cons (nat_lit 1) (List.cons (nat_lit 4) ih))))
      (Nat.beq k (nat_lit 4))) w

@[expose] noncomputable def rowsW (N6 : Nat) (w : List Nat) : Nat :=
  orN (nat_lit 22) fun t => Nat.shiftLeft (wact N6 w (pw2 t)) (Nat.mul (nat_lit 22) t)

@[expose] noncomputable def getW (l : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih j => Nat.rec (motive := fun _ => List Nat) x (fun j' _ => ih j') j) l

@[expose] noncomputable def xsel (V m : Nat) : Nat :=
  xorN (nat_lit 21) fun j => nIf(bit m j, fget V j (nat_lit 22), nat_lit 0)

@[expose] noncomputable def par (x : Nat) : Nat :=
  (fun a => (fun b => (fun c => (fun e => Nat.land (Nat.xor e (Nat.shiftRight e (nat_lit 1))) (nat_lit 1))
      (Nat.xor c (Nat.shiftRight c (nat_lit 2))))
    (Nat.xor b (Nat.shiftRight b (nat_lit 4))))
    (Nat.xor a (Nat.shiftRight a (nat_lit 8))))
  (Nat.xor (Nat.land x (nat_lit 4294967295)) (Nat.shiftRight (Nat.land x (nat_lit 4294967295)) (nat_lit 16)))

@[expose] noncomputable def vecs (N6 : Nat) (cyc : List (List Nat)) (v0 : Nat) : Nat :=
  orN (nat_lit 21) fun j => Nat.shiftLeft (wact N6 (getW cyc j) v0) (Nat.mul (nat_lit 22) j)

@[expose] noncomputable def mats (N6 : Nat) (cyc : List (List Nat)) (dl : Bool) : Nat :=
  orN (nat_lit 21) fun j => Nat.shiftLeft
    (rowsW N6 (Bool.rec (motive := fun _ => List Nat) (getW cyc j) (delta (getW cyc j)) dl))
    (Nat.mul (nat_lit 484) j)

@[expose] noncomputable def matJ (Rs j : Nat) : Nat := fget Rs j (nat_lit 484)

@[expose] noncomputable def linMaps (N6 Rs σ G : Nat) : Nat :=
  Nat.lor (orN (nat_lit 22) fun t =>
      Nat.shiftLeft (xorN (nat_lit 21) fun j => nIf(bit σ j, rowG (matJ Rs j) t, nat_lit 0))
        (Nat.mul (nat_lit 22) t))
    (orN (nat_lit 21) fun i => Nat.shiftLeft
      (orN (nat_lit 22) fun t => Nat.shiftLeft
        (Nat.xor (xorN (nat_lit 21) fun j => nIf(bit (fget G i (nat_lit 22)) j, rowG (matJ Rs j) t, nat_lit 0))
          (act (mat N6 (nat_lit 0)) (rowG (matJ Rs i) t)))
        (Nat.mul (nat_lit 22) t))
      (Nat.mul (nat_lit 484) (Nat.succ i)))

@[expose] noncomputable def combAt (Ms U s : Nat) : Nat :=
  par (xorN (nat_lit 22) fun m => Nat.land (rowG (matJ Ms m) s) (fget U m (nat_lit 22)))

@[expose] noncomputable def infeasOK (Ms U rhs : Nat) : Bool :=
  andB (allN (nat_lit 22) fun s => Nat.beq (combAt Ms U s) (nat_lit 0))
    (Nat.beq (par (Nat.land rhs (fget U (nat_lit 0) (nat_lit 22)))) (nat_lit 1))

@[expose] noncomputable def uniqOK (Ms C rhs sol : Nat) : Bool :=
  allN (nat_lit 22) fun t => (fun U => andB
      (allN (nat_lit 22) fun s => Nat.beq (combAt Ms U s) (nIf(Nat.beq s t, nat_lit 1, nat_lit 0)))
      (Nat.beq (par (Nat.land rhs (fget U (nat_lit 0) (nat_lit 22))))
        (Nat.land (Nat.shiftRight sol t) (nat_lit 1))))
    (fget C t (nat_lit 484))

@[expose] noncomputable def indepOK (V W : Nat) : Bool :=
  allN (nat_lit 21) fun i => allN (nat_lit 21) fun j =>
    Nat.beq (par (Nat.land (fget V i (nat_lit 22)) (fget W j (nat_lit 22))))
      (nIf(Nat.beq i j, nat_lit 1, nat_lit 0))

@[expose] noncomputable def bindRow (M : Nat) (r : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun t => Nat.beq t (nat_lit 22))
    (fun x _ ih t => andB (Nat.blt x (nat_lit 4194304)) (andB (Nat.beq x (rowG M t)) (ih (Nat.succ t))))
    r (nat_lit 0)

@[expose] noncomputable def bindM (N6 : Nat) (A : Array (Array Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k (nat_lit 17))
    (fun r _ ih k => andB (bindRow (mat N6 k) r.toList) (ih (Nat.succ k))) A.toList (nat_lit 0)

@[expose] noncomputable def bindA (P w n : Nat) (A : Array Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k n)
    (fun x _ ih k => andB (Nat.blt x (pw2 w)) (andB (Nat.beq x (fget P k w)) (ih (Nat.succ k))))
    A.toList (nat_lit 0)

@[expose] noncomputable def checkD (N6 GD CD : Nat) (cyc : List (List Nat)) : Bool :=
  strictB (mats N6 cyc true) fun Rs => strictB (vecs N6 cyc (nat_lit 155)) fun V =>
    andB (Nat.beq (xsel V (nat_lit 3112)) (nat_lit 6144))
      (andB (allN (nat_lit 21) fun i =>
          Nat.beq (act (mat N6 (nat_lit 0)) (fget V i (nat_lit 22))) (xsel V (fget GD i (nat_lit 22))))
        (strictB (linMaps N6 Rs (nat_lit 3112) GD) fun Ms => infeasOK Ms CD (nat_lit 6144)))

@[expose] noncomputable def checkI (N6 GI CI WI UM U20 : Nat) (cyc : List (List Nat)) : Bool :=
  strictB (mats N6 cyc false) fun Rs => strictB (vecs N6 cyc (nat_lit 714762)) fun V =>
    andB (Nat.beq (xsel V (nat_lit 3989)) (nat_lit 6144))
      (andB (allN (nat_lit 21) fun i =>
          Nat.beq (act (mat N6 (nat_lit 0)) (fget V i (nat_lit 22))) (xsel V (fget GI i (nat_lit 22))))
        (andB (indepOK V WI)
          (andB (strictB (linMaps N6 Rs (nat_lit 3989) GI) fun Ms =>
              uniqOK Ms CI (nat_lit 6144) (nat_lit 714762))
            (allN (nat_lit 20) fun t =>
              Nat.beq (xsel V (fget UM t (nat_lit 22))) (fget U20 t (nat_lit 22))))))

end CFSG.KC.S23

end
