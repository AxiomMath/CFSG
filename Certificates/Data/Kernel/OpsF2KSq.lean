module

public import Certificates.Data.Kernel.OpsF2K
public import Certificates.Data.CFSGNative.SectionRank.Local

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native

@[expose] def distinctK : List Nat → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !(Nat.beq x y)) && distinctK xs

@[expose] noncomputable def sqK (d A B : Nat) (D : SqData) : Bool :=
  let R := runK d A B D.nregs D.prog
  let X := getR d R D.rx
  let Y := getR d R D.ry
  let H := getR d R D.rh
  let u := pw2 D.t
  seedsOK d A B && D.prog.all expOK && decide (D.t < d) &&
    [D.r, D.oh, D.a, D.b, D.c, D.d].all (decide <| · < 65536) &&
    decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && decide (D.rx < D.nregs) &&
    decide (D.ry < D.nregs) && decide (D.rh < D.nregs) && decide (0 < D.r) &&
    decide (0 < D.oh) && Nat.beq (powK d X D.r) (idF d) && Nat.beq (powK d Y D.r) (idF d) &&
    Nat.beq (powK d H D.oh) (idF d) && commK d X Y &&
    conjK d H X (mulF d (powK d X D.a) (powK d Y D.c)) &&
    conjK d H Y (mulF d (powK d X D.b) (powK d Y D.d)) &&
    distinctK ((List.range (D.r ^ 2)).map fun n => appBaseK d D.r [X, Y] n u)

end CFSG.KC.OpsF2K

end
