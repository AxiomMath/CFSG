module

public import Certificates.Data.Kernel.LocalQT.Sec
public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.KFCub2

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native

@[expose] noncomputable def powN (c : Lay) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => c.ONE)
    (fun _ ih X e =>
      Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat)
          (CFSG.KC.Loop.strictN (c.mul X X) fun X2 =>
            CFSG.KC.Loop.strictN (ih X2 (Nat.div e 2)) fun Y =>
              Bool.rec (motive := fun _ => Nat) Y (c.mul X Y) (Nat.beq (Nat.mod e 2) 1))
          X (Nat.beq e 1))
        c.ONE (Nat.beq e 0)) f

@[expose] noncomputable def powK (c : Lay) (X e : Nat) : Nat := powN c 17 X e

@[expose] def getR (c : Lay) (R : List Nat) (i : Nat) : Nat := R.getD i c.ONE

@[expose] noncomputable def stepV (c : Lay) (R : List Nat) : Op → Nat
  | .mul i j _ => c.mul (getR c R i) (getR c R j)
  | .pow e i _ => powK c (getR c R i) e

@[expose] def Op.tgt : Op → Nat
  | .mul _ _ k => k
  | .pow _ _ k => k

@[expose] noncomputable def runC (c : Lay) (prog : List Op) : List Nat → (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → (List Nat → Bool) → Bool) (fun R k => k R)
    (fun o _ ih R k => strictB (stepV c R o) fun v => ih (R.set (Op.tgt o) v) k) prog

@[expose] def initR (c : Lay) (A B n : Nat) : List Nat :=
  (List.range n).map fun r => if r = 0 then A else if r = 1 then B else c.ONE

@[expose] def expOK : Op → Bool
  | .mul _ _ _ => true
  | .pow e _ _ => decide (e < 65536)

@[expose] noncomputable def appBaseK (c : Lay) (b : Nat) : List Nat → Nat → Nat → Nat
  | [], _, v => v
  | X :: xs, n, v => appBaseK c b xs (n / b) (c.vpow X v (n % b))

@[expose] def allDistinct : List Nat → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !(Nat.beq x y)) && allDistinct xs

@[expose] noncomputable def normalK (c : Lay) (b : Nat) (xs : List Nat) (t : Nat) : Bool :=
  allDistinct ((List.range (b ^ xs.length)).map fun n => appBaseK c b xs n (c.unit t))

@[expose] noncomputable def commK (c : Lay) (X Y : Nat) : Bool := Nat.beq (c.mul X Y) (c.mul Y X)

@[expose] noncomputable def conjK (c : Lay) (X Y W : Nat) : Bool :=
  Nat.beq (c.mul X Y) (c.mul W X)

@[expose] noncomputable def commMK (c : Lay) (r X Y : Nat) : Nat :=
  c.mul (c.mul (c.mul X Y) (powK c X (r - 1))) (powK c Y (r - 1))

@[expose] def progOK (nregs : Nat) (prog : List Op) : Bool :=
  prog.all expOK && decide (2 ≤ nregs) && prog.all (Op.lt nregs)

@[expose] noncomputable def commsK (c : Lay) : List Nat → Bool
  | [] => true
  | X :: xs => xs.all (commK c X) && commsK c xs

@[expose] noncomputable def elemK (c : Lay) (xs tests : List Nat) : Bool :=
  xs.all (fun X => Nat.beq (c.mul (c.mul X X) X) c.ONE) && commsK c xs &&
    (List.range (3 ^ xs.length - 1)).all fun n =>
      tests.any fun k => !Nat.beq (appBaseK c 3 xs (n + 1) (c.unit k)) (c.unit k)

@[expose] noncomputable def commsModK (c : Lay) (T : Nat) : List Nat → Bool
  | [] => true
  | X :: xs => xs.all (fun Y => Nat.beq (c.mul X Y) (c.mul Y X) ||
      Nat.beq (c.mul X Y) (c.mul T (c.mul Y X))) && commsModK c T xs

@[expose] noncomputable def secK (c : Lay) (A B : Nat) (D : SecData) : Bool :=
  progOK D.nregs D.prog && D.outs.all (decide <| · < D.nregs) && decide (D.tReg < D.nregs) &&
    D.tests.all (decide <| · < c.d) &&
  runC c D.prog (initR c A B D.nregs) fun R =>
    let T := getR c R D.tReg
    let xs := D.outs.map (getR c R)
    Nat.beq (c.mul T T) c.ONE &&
      xs.all (fun X => Nat.beq (c.mul X T) (c.mul T X) &&
        (Nat.beq (c.mul X X) c.ONE || Nat.beq (c.mul X X) T)) &&
      commsModK c T xs &&
      (List.range (2 ^ xs.length - 1)).all fun n =>
        D.tests.any (fun k => !Nat.beq (appBaseK c 2 xs (n + 1) (c.unit k)) (c.unit k)) &&
          D.tests.any (fun k => !Nat.beq (appBaseK c 2 xs (n + 1) (c.unit k)) (c.vec (c.unit k) T))

@[expose] noncomputable def sqK (c : Lay) (A B : Nat) (D : SqData) : Bool :=
  progOK D.nregs D.prog && decide (D.rx < D.nregs) && decide (D.ry < D.nregs) &&
    decide (D.rh < D.nregs) && decide (0 < D.r) && decide (0 < D.oh) &&
    [D.r, D.oh, D.a, D.b, D.c, D.d].all (decide <| · < 65536) && decide (D.t < c.d) &&
  runC c D.prog (initR c A B D.nregs) fun R =>
    let X := getR c R D.rx
    let Y := getR c R D.ry
    let H := getR c R D.rh
    Nat.beq (powK c X D.r) c.ONE && Nat.beq (powK c Y D.r) c.ONE &&
      Nat.beq (powK c H D.oh) c.ONE && commK c X Y &&
      conjK c H X (c.mul (powK c X D.a) (powK c Y D.c)) &&
      conjK c H Y (c.mul (powK c X D.b) (powK c Y D.d)) && normalK c D.r [X, Y] D.t

@[expose] noncomputable def cubK (c : Lay) (A B : Nat) (D : CubData) : Bool :=
  progOK D.nregs D.prog && decide (D.rx < D.nregs) && decide (D.ry < D.nregs) &&
    decide (D.rh < D.nregs) && decide (0 < D.r) && decide (0 < D.oh) &&
    [D.r, D.oh, D.a, D.b, D.c, D.d, D.k, D.l, D.μ].all (decide <| · < 65536) &&
    decide (D.t < c.d) &&
  runC c D.prog (initR c A B D.nregs) fun R =>
    let X := getR c R D.rx
    let Y := getR c R D.ry
    let H := getR c R D.rh
    strictB (commMK c D.r X Y) fun Z =>
    Nat.beq (powK c X D.r) c.ONE && Nat.beq (powK c Y D.r) c.ONE &&
      Nat.beq (powK c H D.oh) c.ONE && !(Nat.beq (c.vec (c.unit D.t) Z) (c.unit D.t)) &&
      commK c Z X && commK c Z Y &&
      conjK c H X (c.mul (c.mul (powK c X D.a) (powK c Y D.b)) (powK c Z D.k)) &&
      conjK c H Y (c.mul (c.mul (powK c X D.c) (powK c Y D.d)) (powK c Z D.l)) &&
      conjK c H Z (powK c Z D.μ) && normalK c D.r [X, Y, Z] D.t

@[expose] noncomputable def normK (c : Lay) (N : Cub2NormData) (nregs : Nat) (R : List Nat)
    (X Y Z : Nat) : Bool :=
  let H := getR c R N.rh
  decide (N.rh < nregs) && decide (0 < N.oh) &&
    [N.oh, N.a, N.b, N.c, N.d, N.k, N.l].all (decide <| · < 65536) &&
    Nat.beq (powK c H N.oh) c.ONE &&
    conjK c H X (c.mul (c.mul (powK c X N.a) (powK c Y N.b)) (powK c Z N.k)) &&
    conjK c H Y (c.mul (c.mul (powK c X N.c) (powK c Y N.d)) (powK c Z N.l))

@[expose] noncomputable def cub2K (c : Lay) (A B : Nat) (D : Cub2Data) : Bool :=
  progOK D.nregs D.prog && decide (D.rx < D.nregs) && decide (D.ry < D.nregs) &&
    decide (0 < D.r) && decide (D.r < 65536) && decide (D.t < c.d) &&
  runC c D.prog (initR c A B D.nregs) fun R =>
    let X := getR c R D.rx
    let Y := getR c R D.ry
    strictB (commMK c D.r X Y) fun Z =>
    Nat.beq (powK c X D.r) c.ONE && Nat.beq (powK c Y D.r) c.ONE &&
      !(Nat.beq (c.vec (c.unit D.t) Z) (c.unit D.t)) && commK c Z X && commK c Z Y &&
      normK c D.h1 D.nregs R X Y Z && normK c D.h2 D.nregs R X Y Z

end CFSG.KC.OpsLayK

end
