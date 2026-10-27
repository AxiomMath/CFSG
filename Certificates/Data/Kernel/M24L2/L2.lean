module

public import Certificates.Data.Kernel.M24L2.Letters
public import Certificates.Data.Kernel.M24L2.Bfs
public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.CGT.M24R.L2InputsD

public section

namespace CFSG.KC.M24L2

open CFSG.CGT.M24R

@[expose] noncomputable def ttC (k : Nat) : Nat := Nat.add k (nat_lit 541200)

@[expose] noncomputable def isTtK (x : Nat) : Bool := Nat.beq x (ttC (x % 16))

@[expose] noncomputable def relCheckK : Bool := relsN8Ten.all fun r => Nat.beq (cwK r) idC

@[expose] noncomputable def tCheckK : Bool :=
  (List.range 16).all (fun k => (List.range 16).all fun l =>
    Nat.beq (mulC (ttC k) (ttC l)) (ttC (k ^^^ l))) &&
  (List.range 16).all (fun k => (List.range 16).all fun l => !(Nat.beq (ttC k) (ttC l)) || k == l) &&
  (List.range 16).all fun k => ttC k % 16 == k

@[expose] noncomputable def tNormCheckK : Bool :=
  (List.finRange 10).all fun j => [true, false].all fun b => (List.range 16).all fun k =>
    (List.range 16).any fun l =>
      Nat.beq (mulC (lcC (j, b)) (ttC k)) (mulC (ttC l) (lcC (j, b)))

@[expose] noncomputable def b0C : Nat := cwK (bWord 0)

@[expose] noncomputable def b1C : Nat := cwK (bWord 1)

@[expose] noncomputable def b01C : Nat := mulC b0C b1C

@[expose] noncomputable def bCheckK : Bool :=
  Nat.beq (mulC b0C b0C) idC && Nat.beq (mulC b1C b1C) idC && commK b0C b1C &&
    !(Nat.beq b0C idC) && !(Nat.beq b1C idC) && !(Nat.beq b0C b1C) && !(Nat.beq b01C idC) &&
    !(Nat.beq b01C b0C) && !(Nat.beq b01C b1C) && !(isTtK b0C)

@[expose] noncomputable def commCountK (x : Nat) : Nat :=
  (List.range 16).countP fun k => commK x (ttC k)

@[expose] noncomputable def validK (G n : Nat) : Bool :=
  Nat.blt n (nat_lit 1048576) &&
    !(Nat.beq (Nat.land G (Nat.shiftLeft (nat_lit 1) (Nat.shiftRight n (nat_lit 4)))) (nat_lit 0))

@[expose] noncomputable def witK (G p : Nat) (W : List (Nat × Nat)) (x : Nat) : Bool :=
  anyL (fun e => Nat.beq e.1 x && validK G e.2 && Nat.beq (mulC e.2 p) (mulC x e.2)) W

@[expose] noncomputable def faBody (G : Nat) (W : List (Nat × Nat)) (c : Nat) : Bool :=
  bIf(Nat.beq (mulC c c) idC,
    bIf(isTtK c, true, bIf(Nat.blt 4 (commCountK c), true, witK G b0C W c)), true)

@[expose] noncomputable def sqLin (m : Nat) : Bool :=
  Nat.beq (mulC (Nat.mul (nat_lit 16) m) (Nat.mul (nat_lit 16) m)) idC

@[expose] noncomputable def faM (G : Nat) (W : List (Nat × Nat)) (m : Nat) : Bool :=
  bIf(sqLin m,
    CFSG.KC.Enum.allN 16 fun v => letN (Nat.add v (Nat.mul (nat_lit 16) m)) fun c => faBody G W c,
    true)

@[expose] noncomputable def kListC (x : Nat) : List Nat := [idC, b0C, x, mulC b0C x]

@[expose] noncomputable def conjInK (x p : Nat) (L : List Nat) : Bool :=
  L.any fun k => Nat.beq (mulC x p) (mulC k x)

@[expose] noncomputable def conjInRK (x p : Nat) (L : List Nat) : Bool :=
  L.any fun k => Nat.beq (mulC p x) (mulC x k)

@[expose] noncomputable def normKK (L : List Nat) (p q x : Nat) : Bool :=
  conjInK x p L && conjInK x q L && conjInRK x p L && conjInRK x q L

@[expose] noncomputable def kleinPreK (x : Nat) : Bool :=
  Nat.beq (mulC x x) idC && commK x b0C && !(isTtK x) && !(isTtK (mulC b0C x)) &&
    !(Nat.beq x b0C)

@[expose] noncomputable def kleinCheapK (x : Nat) : Bool :=
  (List.range 16).countP (fun k => normKK (kListC x) b0C x (ttC k)) == 4 &&
  (List.range 16).all (fun k => !(normKK (kListC x) b0C x (ttC k)) ||
    (commK (ttC k) b0C && commK (ttC k) x)) &&
  (List.range 16).all fun k =>
    !(commK (ttC k) b0C || commK (ttC k) x || commK (ttC k) (mulC b0C x)) ||
      normKK (kListC x) b0C x (ttC k)

@[expose] noncomputable def isBtK (x : Nat) : Bool := [idC, b0C, b1C, b01C].contains x

@[expose] noncomputable def refutesK (x y : Nat) : Bool :=
  (commK y b0C || commK y x || commK y (mulC b0C x)) && !(normKK (kListC x) b0C x y)

@[expose] noncomputable def fbWit (G : Nat) (W : List (Nat × Nat)) (x : Nat) : Bool :=
  anyL (fun e => Nat.beq e.1 x && validK G e.2 && refutesK x e.2) W

@[expose] noncomputable def fbBody (G : Nat) (W : List (Nat × Nat)) (c : Nat) : Bool :=
  bIf(kleinPreK c, bIf(kleinCheapK c, bIf(isBtK c, true, fbWit G W c), true), true)

@[expose] noncomputable def fbM (G : Nat) (W : List (Nat × Nat)) (m : Nat) : Bool :=
  bIf(sqLin m,
    CFSG.KC.Enum.allN 16 fun v => letN (Nat.add v (Nat.mul (nat_lit 16) m)) fun c => fbBody G W c,
    true)

@[expose] noncomputable def fbE (G : Nat) (W : List (Nat × Nat)) (E : List (Nat × Nat × Nat)) :
    Bool :=
  fbM G W (nat_lit 33825) && allL (fun e => letN e.1 fun m => fbM G W m) E

@[expose] noncomputable def faE (G : Nat) (W : List (Nat × Nat)) (E : List (Nat × Nat × Nat)) :
    Bool :=
  faM G W (nat_lit 33825) && allL (fun e => letN e.1 fun m => faM G W m) E

end CFSG.KC.M24L2
