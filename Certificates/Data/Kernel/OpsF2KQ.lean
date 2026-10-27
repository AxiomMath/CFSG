module

public import Certificates.Data.Kernel.OpsF2KFusQ

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native
open CFSG.KC.Misc.G24 (mulF2)

@[expose] noncomputable def commQ (d X Y : Nat) : Bool := Nat.beq (mulF2 d X Y) (mulF2 d Y X)

@[expose] noncomputable def conjQ (d X Y W : Nat) : Bool := Nat.beq (mulF2 d X Y) (mulF2 d W X)

@[expose] noncomputable def commMQ (d r X Y : Nat) : Nat :=
  mulF2 d (mulF2 d (mulF2 d X Y) (pqK d X (r - 1))) (pqK d Y (r - 1))

@[expose] noncomputable def commsModQ (d T : Nat) : List Nat → Bool
  | [] => true
  | X :: xs => xs.all (fun Y => Nat.beq (mulF2 d X Y) (mulF2 d Y X) ||
      Nat.beq (mulF2 d X Y) (mulF2 d T (mulF2 d Y X))) && commsModQ d T xs

@[expose] noncomputable def secQ (d A B : Nat) (D : SecData) : Bool :=
  let R := runQ d A B D.nregs D.prog
  let T := getR d R D.tReg
  let xs := D.outs.map (getR d R)
  seedsOK d A B && D.prog.all expOK && decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) &&
    D.outs.all (decide <| · < D.nregs) && decide (D.tReg < D.nregs) &&
    D.tests.all (decide <| · < d) && Nat.beq (mulF2 d T T) (idF d) &&
    xs.all (fun X => Nat.beq (mulF2 d X T) (mulF2 d T X) &&
      (Nat.beq (mulF2 d X X) (idF d) || Nat.beq (mulF2 d X X) T)) &&
    commsModQ d T xs &&
    (List.range (2 ^ xs.length - 1)).all fun n =>
      D.tests.any (fun k => !Nat.beq (appBaseK d 2 xs (n + 1) (pw2 k)) (pw2 k)) &&
        D.tests.any (fun k => !Nat.beq (appBaseK d 2 xs (n + 1) (pw2 k)) (vmF d T (pw2 k)))

@[expose] noncomputable def commsQ (d : Nat) : List Nat → Bool
  | [] => true
  | X :: xs => xs.all (commQ d X) && commsQ d xs

@[expose] noncomputable def w4Q (d A B : Nat) (D : Data) (inv : Nat) : Bool :=
  let R := runQ d A B D.nregs D.prog
  let xs := D.outs.map (getR d R)
  let T := getR d R inv
  seedsOK d A B && D.prog.all expOK && decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) &&
    D.outs.all (decide <| · < D.nregs) && decide (inv < D.nregs) &&
    D.tests.all (decide <| · < d) &&
    xs.all (fun X => Nat.beq (mulF2 d (mulF2 d X X) X) (idF d)) && commsQ d xs &&
    ((List.range (3 ^ xs.length - 1)).all fun n =>
      D.tests.any fun k => !Nat.beq (appBaseK d 3 xs (n + 1) (pw2 k)) (pw2 k)) &&
    Nat.beq (mulF2 d T T) (idF d) &&
    D.tests.any (fun k => !Nat.beq (vmF d T (pw2 k)) (pw2 k)) &&
    D.outs.all (fun r => commQ d (getR d R r) T)

@[expose] noncomputable def normQ (d : Nat) (N : Cub2NormData) (nregs : Nat) (R : List Nat)
    (X Y Z : Nat) : Bool :=
  let H := getR d R N.rh
  decide (N.rh < nregs) && decide (0 < N.oh) &&
    [N.oh, N.a, N.b, N.c, N.d, N.k, N.l].all (decide <| · < 65536) &&
    Nat.beq (pqK d H N.oh) (idF d) &&
    conjQ d H X (mulF2 d (mulF2 d (pqK d X N.a) (pqK d Y N.b)) (pqK d Z N.k)) &&
    conjQ d H Y (mulF2 d (mulF2 d (pqK d X N.c) (pqK d Y N.d)) (pqK d Z N.l))

@[expose] noncomputable def cub2Q (d A B : Nat) (D : Cub2Data) : Bool :=
  let R := runQ d A B D.nregs D.prog
  let X := getR d R D.rx
  let Y := getR d R D.ry
  let Z := commMQ d D.r X Y
  seedsOK d A B && D.prog.all expOK && decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) &&
    decide (D.rx < D.nregs) && decide (D.ry < D.nregs) && decide (0 < D.r) &&
    decide (D.r < 65536) && decide (D.t < d) &&
    Nat.beq (pqK d X D.r) (idF d) && Nat.beq (pqK d Y D.r) (idF d) &&
    !(Nat.beq (vmF d Z (pw2 D.t)) (pw2 D.t)) &&
    commQ d Z X && commQ d Z Y &&
    normQ d D.h1 D.nregs R X Y Z && normQ d D.h2 D.nregs R X Y Z

end CFSG.KC.OpsF2K

end
