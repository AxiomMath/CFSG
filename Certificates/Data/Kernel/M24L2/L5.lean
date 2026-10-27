module

public import Certificates.Data.Kernel.M24L2.L2
public import CFSG.CGT.L5R.L2InputsLD

public section

namespace CFSG.KC.M24L2

open CFSG.CGT.L5R CFSG.CGT.M24R CFSG.KC.Enum

@[expose] noncomputable def betaC (i : Fin 3) : Nat := cwK (betaW10 i)

@[expose] noncomputable def gamC : Nat := cwK gammaW10

@[expose] noncomputable def d2C (i : Fin 2) : Nat := cwK (dW10 i)

@[expose] noncomputable def th2C (i : Fin 2) : Nat := cwK (thW10 i)

@[expose] noncomputable def nzC : Nat := cwK nzW10

@[expose] noncomputable def eightC (p q r : Nat) : List Nat :=
  [idC, p, q, mulC p q, r, mulC p r, mulC q r, mulC (mulC p q) r]

@[expose] noncomputable def b8C : List Nat := eightC (betaC 0) (betaC 1) (betaC 2)

@[expose] noncomputable def isB8K (x : Nat) : Bool := b8C.contains x

@[expose] noncomputable def normAllK (L : List Nat) (x : Nat) : Bool :=
  L.all fun p => conjInK x p L && conjInRK x p L

@[expose] noncomputable def bCheckLK : Bool :=
  decide b8C.Nodup && b8C.all (fun x => Nat.beq (mulC x x) idC) &&
    b8C.all (fun x => b8C.all fun y => b8C.contains (mulC x y)) &&
    b8C.tail.all (fun x => !(isTtK x)) && !(isTtK gamC)

@[expose] noncomputable def faLBody (G : Nat) (W1 W2 : List (Nat × Nat)) (c : Nat) : Bool :=
  bIf(Nat.beq (mulC c c) idC,
    bIf(isTtK c, true,
      bIf(commCountK c == 8, witK G (betaC 0) W1 c || witK G gamC W2 c, true)), true)

@[expose] noncomputable def faLM (G : Nat) (W1 W2 : List (Nat × Nat)) (m : Nat) : Bool :=
  bIf(sqLin m,
    allN 16 fun v => letN (Nat.add v (Nat.mul (nat_lit 16) m)) fun c => faLBody G W1 W2 c, true)

@[expose] noncomputable def candLK (p x : Nat) : Bool :=
  Nat.beq (mulC x x) idC && commK x p && !(isTtK x) && !(Nat.beq x p) &&
    !(isTtK (mulC p x)) && (List.range 16).all fun k => commK (ttC k) x == commK (ttC k) p

@[expose] noncomputable def pairPreK (p x y : Nat) : Bool :=
  commK x y && !(Nat.beq y p) && !(Nat.beq y x) && !(Nat.beq y (mulC p x)) &&
    candLK p (mulC x y) && candLK p (mulC (mulC p x) y)

@[expose] noncomputable def refLK (L : List Nat) (x y z : Nat) : Bool :=
  !(conjInK z x L) || !(conjInK z y L)

@[expose] noncomputable def fbLWit (G p : Nat) (W : List ((Nat × Nat) × Nat)) (x y : Nat) : Bool :=
  anyL (fun e => Nat.beq e.1.1 x && Nat.beq e.1.2 y && validK G e.2 && commK e.2 p &&
    refLK (eightC p x y) x y e.2) W

@[expose] noncomputable def fbPairK (G p : Nat) (allowB : Bool) (W : List ((Nat × Nat) × Nat))
    (x y : Nat) : Bool :=
  bIf(pairPreK p x y, decide (eightC p x y).Nodup &&
    ((allowB && isB8K x && isB8K y) || fbLWit G p W x y), true)

@[expose] noncomputable def fbLK (G p : Nat) (allowB : Bool) (Cd : List Nat)
    (W : List ((Nat × Nat) × Nat)) : Bool :=
  allL (fun x => allL (fun y => fbPairK G p allowB W x y) Cd) Cd

@[expose] noncomputable def candM (p : Nat) (Cd : List Nat) (m : Nat) : Bool :=
  bIf(sqLin m,
    allN 16 fun v => letN (Nat.add v (Nat.mul (nat_lit 16) m)) fun c =>
      bIf(candLK p c, Cd.contains c, true), true)

@[expose] noncomputable def ev2K (u : Fin 2 → Nat) (w : List (Fin 2)) : Nat :=
  foldL (fun c k => mulC c (u k)) w idC

@[expose] noncomputable def dPart1L : Bool :=
  (List.finRange 2).all fun i => normAllK b8C (d2C i) && normAllK b8C (th2C i)

@[expose] noncomputable def dBodyL (c : Nat) : Bool :=
  bIf(normAllK b8C c, !(commK c (d2C 0)) || !(commK c (d2C 1)) || Nat.beq c idC, true)

@[expose] noncomputable def dLinL (m : Nat) : Bool :=
  commK (Nat.mul (nat_lit 16) m) (Nat.mul (nat_lit 16) (Nat.shiftRight (d2C 0) (nat_lit 4))) &&
  commK (Nat.mul (nat_lit 16) m) (Nat.mul (nat_lit 16) (Nat.shiftRight (d2C 1) (nat_lit 4)))

@[expose] noncomputable def dML (m : Nat) : Bool :=
  bIf(dLinL m, allN 16 fun v => letN (Nat.add v (Nat.mul (nat_lit 16) m)) fun c => dBodyL c, true)

@[expose] noncomputable def dPart3L : Bool :=
  (List.finRange 2).all fun i =>
    Nat.beq (ev2K d2C (thDW i)) (th2C i) && Nat.beq (ev2K th2C (thDW i)) (d2C i)

@[expose] noncomputable def wCheckLK : Bool :=
  relDW.all (fun p => Nat.beq (ev2K d2C p.1) (ev2K d2C p.2)) && !(Nat.beq (d2C 0) idC) &&
    Nat.beq (ev2K d2C sevenW) idC &&
    (List.finRange 3).all (fun i => !(Nat.beq (ev2K d2C (aDW i)) idC) && isTtK (ev2K d2C (aDW i))) &&
    (List.finRange 3).all (fun i => !(Nat.beq (ev2K d2C (bDW i)) idC) && isB8K (ev2K d2C (bDW i))) &&
    conjInK nzC (ev2K d2C z1DW) b8C && !(isTtK (ev2K d2C z2DW)) &&
    commCountK (ev2K d2C z2DW) == 4

@[expose] noncomputable def dLinB8 (m : Nat) : Bool :=
  b8C.any fun k =>
    Nat.beq (mulC (Nat.mul (nat_lit 16) m) (Nat.mul (nat_lit 16) (Nat.shiftRight (betaC 0) (nat_lit 4))))
      (mulC (Nat.mul (nat_lit 16) (Nat.shiftRight k (nat_lit 4))) (Nat.mul (nat_lit 16) m))

@[expose] noncomputable def s0Wit (G : Nat) (W : List (Nat × Nat × Nat)) (c : Nat) : Bool :=
  anyL (fun e => Nat.beq e.1 c && validK G e.2.1 && normAllK b8C e.2.1 &&
    bIf(Nat.beq e.2.2 1, Nat.beq (mulC e.2.1 c) (mulC (th2C 0) e.2.1),
      Nat.beq (mulC e.2.1 c) (mulC rep2Code e.2.1))) W

@[expose] noncomputable def s0Body (G : Nat) (W : List (Nat × Nat × Nat)) (c : Nat) : Bool :=
  bIf(normAllK b8C c,
    bIf(Nat.beq c idC, true,
      bIf(Nat.beq (ev2K (fun _ => c) sevenW) idC, s0Wit G W c, true)), true)

@[expose] noncomputable def s0M (G : Nat) (W : List (Nat × Nat × Nat)) (m : Nat) : Bool :=
  bIf(dLinB8 m,
    allN 16 fun v => letN (Nat.add v (Nat.mul (nat_lit 16) m)) fun c => s0Body G W c, true)

@[expose] noncomputable def first4K (u : Fin 2 → Nat) : Bool :=
  relDW.all (fun p => Nat.beq (ev2K u p.1) (ev2K u p.2)) &&
    (List.finRange 3).all (fun i => !(Nat.beq (ev2K u (aDW i)) idC) && isB8K (ev2K u (aDW i))) &&
    (List.finRange 3).all (fun i => !(Nat.beq (ev2K u (bDW i)) idC) && isTtK (ev2K u (bDW i))) &&
    (isTtK (ev2K u z1DW) || !(commCountK (ev2K u z1DW) == 4))

@[expose] noncomputable def powK (r : Nat) : Nat → Nat
  | 0 => idC
  | k + 1 => mulC r (powK r k)

@[expose] noncomputable def disjK (r c : Nat) : Bool :=
  Nat.beq r (th2C 0) && (List.range 7).any fun k =>
    Nat.beq (mulC (powK (th2C 0) k) c) (mulC (th2C 1) (powK (th2C 0) k))

@[expose] noncomputable def s1Wit (G : Nat) (W : List ((Nat × Nat) × Nat)) (i r c : Nat) : Bool :=
  anyL (fun e => Nat.beq e.1.1 i && Nat.beq e.1.2 c && validK G e.2 &&
    Nat.beq (mulC e.2 (betaC 0)) (mulC (ev2K ![r, c] z2DW) e.2)) W

@[expose] noncomputable def s1Body (G : Nat) (W : List ((Nat × Nat) × Nat)) (i r c : Nat) : Bool :=
  bIf(normAllK b8C c,
    bIf(first4K ![r, c], bIf(disjK r c, true, s1Wit G W i r c), true), true)

@[expose] noncomputable def s1M (G : Nat) (W : List ((Nat × Nat) × Nat)) (m : Nat) : Bool :=
  bIf(dLinB8 m,
    allN 16 fun v => letN (Nat.add v (Nat.mul (nat_lit 16) m)) fun c =>
      s1Body G W 0 (th2C 0) c && s1Body G W 1 rep2Code c, true)

@[expose] noncomputable def sliceL (Q : Nat → Bool) (E : List (Nat × Nat × Nat)) : Bool :=
  Q (nat_lit 33825) && allL (fun e => letN e.1 fun m => Q m) E

end CFSG.KC.M24L2
