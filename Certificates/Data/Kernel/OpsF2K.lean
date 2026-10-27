module

public import Certificates.Data.Kernel.M1F2
public import Certificates.Data.CFSGNative.SectionRank.Elem3
public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.KFCub2

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native

@[expose] noncomputable def powK (d X e : Nat) : Nat := powF d X e 16

@[expose] noncomputable def getR (d : Nat) (R : List Nat) (i : Nat) : Nat := R.getD i (idF d)

@[expose] noncomputable def stepK (d : Nat) (R : List Nat) : Op → List Nat
  | .mul i j k => R.set k (mulF d (getR d R i) (getR d R j))
  | .pow e i k => R.set k (powK d (getR d R i) e)

@[expose] def expOK : Op → Bool
  | .mul _ _ _ => true
  | .pow e _ _ => decide (e < 65536)

@[expose] noncomputable def runK (d A B n : Nat) (prog : List Op) : List Nat :=
  prog.foldl (stepK d) ((List.range n).map fun r => if r = 0 then A else if r = 1 then B else idF d)

@[expose] noncomputable def appK (d X : Nat) : Nat → Nat → Nat
  | 0, v => v
  | n + 1, v => appK d X n (vmF d X v)

@[expose] noncomputable def appBaseK (d b : Nat) : List Nat → Nat → Nat → Nat
  | [], _, v => v
  | X :: xs, n, v => appBaseK d b xs (n / b) (appK d X (n % b) v)

@[expose] def seedsOK (d A B : Nat) : Bool :=
  decide (0 < d) && decide (A < 2 ^ (d * d)) && decide (B < 2 ^ (d * d))

@[expose] noncomputable def commK (d X Y : Nat) : Bool := Nat.beq (mulF d X Y) (mulF d Y X)

@[expose] noncomputable def conjK (d X Y W : Nat) : Bool := Nat.beq (mulF d X Y) (mulF d W X)

@[expose] noncomputable def commMK (d r X Y : Nat) : Nat :=
  mulF d (mulF d (mulF d X Y) (powK d X (r - 1))) (powK d Y (r - 1))

@[expose] noncomputable def commsModK (d T : Nat) : List Nat → Bool
  | [] => true
  | X :: xs => xs.all (fun Y => Nat.beq (mulF d X Y) (mulF d Y X) ||
      Nat.beq (mulF d X Y) (mulF d T (mulF d Y X))) && commsModK d T xs

@[expose] noncomputable def secK (d A B : Nat) (D : SecData) : Bool :=
  let R := runK d A B D.nregs D.prog
  let T := getR d R D.tReg
  let xs := D.outs.map (getR d R)
  seedsOK d A B && D.prog.all expOK && decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) &&
    D.outs.all (decide <| · < D.nregs) && decide (D.tReg < D.nregs) &&
    D.tests.all (decide <| · < d) && Nat.beq (mulF d T T) (idF d) &&
    xs.all (fun X => Nat.beq (mulF d X T) (mulF d T X) &&
      (Nat.beq (mulF d X X) (idF d) || Nat.beq (mulF d X X) T)) &&
    commsModK d T xs &&
    (List.range (2 ^ xs.length - 1)).all fun n =>
      D.tests.any (fun k => !Nat.beq (appBaseK d 2 xs (n + 1) (pw2 k)) (pw2 k)) &&
        D.tests.any (fun k => !Nat.beq (appBaseK d 2 xs (n + 1) (pw2 k)) (vmF d T (pw2 k)))

@[expose] noncomputable def commsK (d : Nat) : List Nat → Bool
  | [] => true
  | X :: xs => xs.all (commK d X) && commsK d xs

@[expose] noncomputable def w4K (d A B : Nat) (D : Data) (inv : Nat) : Bool :=
  let R := runK d A B D.nregs D.prog
  let xs := D.outs.map (getR d R)
  let T := getR d R inv
  seedsOK d A B && D.prog.all expOK && decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) &&
    D.outs.all (decide <| · < D.nregs) && decide (inv < D.nregs) &&
    D.tests.all (decide <| · < d) &&
    xs.all (fun X => Nat.beq (mulF d (mulF d X X) X) (idF d)) && commsK d xs &&
    ((List.range (3 ^ xs.length - 1)).all fun n =>
      D.tests.any fun k => !Nat.beq (appBaseK d 3 xs (n + 1) (pw2 k)) (pw2 k)) &&
    Nat.beq (mulF d T T) (idF d) &&
    D.tests.any (fun k => !Nat.beq (vmF d T (pw2 k)) (pw2 k)) &&
    D.outs.all (fun r => commK d (getR d R r) T)

@[expose] noncomputable def normK (d : Nat) (N : Cub2NormData) (nregs : Nat) (R : List Nat)
    (X Y Z : Nat) : Bool :=
  let H := getR d R N.rh
  decide (N.rh < nregs) && decide (0 < N.oh) &&
    [N.oh, N.a, N.b, N.c, N.d, N.k, N.l].all (decide <| · < 65536) &&
    Nat.beq (powK d H N.oh) (idF d) &&
    conjK d H X (mulF d (mulF d (powK d X N.a) (powK d Y N.b)) (powK d Z N.k)) &&
    conjK d H Y (mulF d (mulF d (powK d X N.c) (powK d Y N.d)) (powK d Z N.l))

@[expose] noncomputable def cub2K (d A B : Nat) (D : Cub2Data) : Bool :=
  let R := runK d A B D.nregs D.prog
  let X := getR d R D.rx
  let Y := getR d R D.ry
  let Z := commMK d D.r X Y
  seedsOK d A B && D.prog.all expOK && decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) &&
    decide (D.rx < D.nregs) && decide (D.ry < D.nregs) && decide (0 < D.r) &&
    decide (D.r < 65536) && decide (D.t < d) &&
    Nat.beq (powK d X D.r) (idF d) && Nat.beq (powK d Y D.r) (idF d) &&
    !(Nat.beq (vmF d Z (pw2 D.t)) (pw2 D.t)) &&
    commK d Z X && commK d Z Y &&
    normK d D.h1 D.nregs R X Y Z && normK d D.h2 D.nregs R X Y Z

end CFSG.KC.OpsF2K

end
