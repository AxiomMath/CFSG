module

public import Certificates.Data.Kernel.Misc.GL4Elt
public import Certificates.Data.Kernel.Misc.PermClos
public import Certificates.Data.Kernel.F4M3B

public section

namespace CFSG.KD.Sp4Cen

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4 CFSG.KC.Misc.Clos

@[expose] noncomputable def f16 (r i : Nat) : Nat :=
  Nat.land (Nat.shiftRight r (Nat.mul (nat_lit 16) i)) (nat_lit 65535)

@[expose] noncomputable def trF (a : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (Nat.land a (nat_lit 33825))
      (Nat.shiftLeft (Nat.land a (nat_lit 2114)) (nat_lit 3)))
    (Nat.lor (Nat.shiftLeft (Nat.land a (nat_lit 132)) (nat_lit 6))
      (Nat.shiftLeft (Nat.land a (nat_lit 8)) (nat_lit 9))))
    (Nat.lor (Nat.lor (Nat.shiftRight (Nat.land a (nat_lit 16912)) (nat_lit 3))
      (Nat.shiftRight (Nat.land a (nat_lit 8448)) (nat_lit 6)))
      (Nat.shiftRight (Nat.land a (nat_lit 4096)) (nat_lit 9)))

@[expose] noncomputable def formF (w g : Nat) : Nat := mul4F (trF g) (mul4F w g)

@[expose] noncomputable def conjF (g x gi : Nat) : Nat := mul4F (mul4F g x) gi

@[expose] noncomputable def relB (a b n : Nat) : Bool := Nat.beq (pow4F (mul4F a b) n) id4

@[expose] noncomputable def invW (g gi : Nat) : Bool :=
  andB (Nat.beq (mul4F g gi) id4) (Nat.beq (mul4F gi g) id4)

@[expose] noncomputable def entP (P : Nat → Nat) (i j : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.land (P (Nat.mul 4 i)) (P j))
      (Nat.land (P (Nat.add (Nat.mul 4 i) 1)) (P (Nat.add 4 j))))
    (Nat.xor (Nat.land (P (Nat.add (Nat.mul 4 i) 2)) (P (Nat.add 8 j)))
      (Nat.land (P (Nat.add (Nat.mul 4 i) 3)) (P (Nat.add 12 j))))

@[expose] noncomputable def sqAcc (P : Nat → Nat) (t : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) t (fun q acc =>
    Nat.land acc (Bool.rec (motive := fun _ => Nat)
      (Nat.xor t (entP P (Nat.div q 4) (Nat.mod q 4))) (entP P (Nat.div q 4) (Nat.mod q 4))
      (Nat.beq (Nat.div q 4) (Nat.mod q 4)))) n

@[expose] noncomputable def sqPlane : Nat :=
  sqAcc (fun b => CFSG.KC.F4M3B.pln b 16) (Nat.sub (Nat.pow 2 (Nat.pow 2 16)) 1) 16

@[expose] noncomputable def indK (E : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.lor acc (Nat.shiftLeft 1 (E k))) n

@[expose] noncomputable def xOf (RI : Nat → Nat) (k : Nat) : Nat := f16 (RI k) 0

@[expose] noncomputable def invK (RI : Nat → Nat) : Bool :=
  andB (allN (nat_lit 315) fun k => Nat.blt (xOf RI k) (xOf RI (Nat.succ k)))
    (Nat.beq sqPlane (indK (xOf RI) (nat_lit 316)))

@[expose] noncomputable def memL (c : Nat) (L : List Nat) : Bool := anyL L fun d => Nat.beq d c

@[expose] noncomputable def a2OK (r : Nat) (reps : List Nat) (x c ci : Nat) : Bool :=
  impB (andB (relB r x 3) (notB (Nat.beq (mul4F r x) id4)))
    (andB (invW c ci) (andB (Nat.beq (mul4F c r) (mul4F r c)) (memL (conjF c x ci) reps)))

@[expose] noncomputable def riAt (RI : Nat → Nat) (r0 r1 : Nat) (reps0 reps1 : List Nat)
    (k : Nat) : Bool :=
  letB (RI k) fun v => letB (f16 v 0) fun x =>
    andB (orB (Nat.beq x id4) (andB (invW (f16 v 1) (f16 v 2))
      (letB (conjF (f16 v 1) x (f16 v 2)) fun y => orB (Nat.beq y r0) (Nat.beq y r1))))
    (andB (a2OK r0 reps0 x (f16 v 3) (f16 v 4)) (a2OK r1 reps1 x (f16 v 5) (f16 v 6)))

@[expose] noncomputable def tup5 (a b c d e : Nat) : Nat :=
  Nat.lor (Nat.lor a (Nat.shiftLeft b 16)) (Nat.lor (Nat.shiftLeft c 32)
    (Nat.lor (Nat.shiftLeft d 48) (Nat.shiftLeft e 64)))

@[expose] noncomputable def leafIn (LF : Nat → Nat) (nL t : Nat) : Bool :=
  anyN nL fun m => Nat.beq (LF m) t

@[expose] noncomputable def srchK (RI LF : Nat → Nat) (nL r a2 : Nat) : Bool :=
  allN (nat_lit 316) fun k3 => letB (xOf RI k3) fun a3 =>
    impB (andB (relB r a3 2) (relB a2 a3 3)) (allN (nat_lit 316) fun k4 => letB (xOf RI k4) fun a4 =>
      impB (andB (relB r a4 2) (andB (relB a2 a4 2) (relB a3 a4 3)))
        (allN (nat_lit 316) fun k5 => letB (xOf RI k5) fun a5 =>
          impB (andB (relB r a5 2) (andB (relB a2 a5 2) (andB (relB a3 a5 2) (relB a4 a5 3))))
            (leafIn LF nL (tup5 r a2 a3 a4 a5))))

@[expose] noncomputable def wordE (L : Nat → Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun acc _ => acc)
    (fun _ ih acc w => Bool.rec (motive := fun _ => Nat)
      (ih (mul4F acc (L (Nat.pred (Nat.land w 7)))) (Nat.shiftRight w 3)) acc
      (Nat.beq (Nat.land w 7) 0)) fuel

@[expose] noncomputable def letF (c ci t : Nat) (i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) id4 (conjF c (f16 t i) ci) (Nat.blt i 5)

@[expose] noncomputable def leafAt (LF LC LW : Nat → Nat) (w0 s0 s1 : Nat) (m : Nat) : Bool :=
  letB (LF m) fun t => letB (f16 (LC m) 0) fun c => letB (f16 (LC m) 1) fun ci =>
    andB (invW c ci) (andB
      (allN 5 fun i => Nat.beq (formF w0 (conjF c (f16 t i) ci)) w0)
      (andB (Nat.beq (wordE (letF c ci t) 22 id4 (Nat.land (LW m)
          (nat_lit 18446744073709551615))) s0)
        (Nat.beq (wordE (letF c ci t) 22 id4 (Nat.shiftRight (LW m) 64)) s1)))

@[expose] noncomputable def blk (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) 2 1 (Nat.blt k 16)) 0
    (Nat.blt k 1)

@[expose] noncomputable def isStart (k : Nat) : Bool :=
  orB (Nat.beq k 0) (orB (Nat.beq k 1) (Nat.beq k 16))

@[expose] noncomputable def formAt (FM FG FP FC G : Nat → Nat) (w0 : Nat) (k : Nat) : Bool :=
  letB (FM k) fun f =>
    andB (andB (invW (f16 (FG k) 0) (f16 (FG k) 1)) (Nat.beq (formF w0 (f16 (FG k) 0)) f))
    (andB (allN (nat_lit 28) fun j => impB (Nat.beq (FM j) f) (Nat.beq j k))
    (andB (orB (isStart k) (letB (FP k) fun r =>
        letB (Nat.land r (nat_lit 16777215)) fun p => letB (Nat.shiftRight r (nat_lit 24)) fun l =>
          andB (Nat.blt p k) (andB (Nat.beq (blk p) (blk k)) (andB (Nat.blt l 2)
            (Nat.beq f (formF (FM p) (G l)))))))
      (allN 2 fun j => letB (FC (Nat.add (Nat.mul k 2) j)) fun t =>
        andB (Nat.blt t (nat_lit 28)) (andB (Nat.beq (blk t) (blk k))
          (Nat.beq (FM t) (formF f (G j)))))))

@[expose] noncomputable def witK (f fi x xi : Nat) : Bool :=
  andB (andB (invW f fi) (invW x xi)) (andB (andB (ordDiv f 5) (ordDiv x 3))
    (Nat.beq (mul4F f x) (mul4F x f)))

end CFSG.KD.Sp4Cen

end
