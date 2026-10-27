module

public import Certificates.Data.Kernel.OpsF2KQ
public import Certificates.Data.Kernel.OpsF2KSq

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native
open CFSG.KC.Misc.G24 (mulF2)

@[expose] noncomputable def sqQ (d A B : Nat) (D : SqData) : Bool :=
  let R := runQ d A B D.nregs D.prog
  let X := getR d R D.rx
  let Y := getR d R D.ry
  let H := getR d R D.rh
  let u := pw2 D.t
  seedsOK d A B && D.prog.all expOK && decide (D.t < d) &&
    [D.r, D.oh, D.a, D.b, D.c, D.d].all (decide <| · < 65536) &&
    decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && decide (D.rx < D.nregs) &&
    decide (D.ry < D.nregs) && decide (D.rh < D.nregs) && decide (0 < D.r) &&
    decide (0 < D.oh) && Nat.beq (pqK d X D.r) (idF d) && Nat.beq (pqK d Y D.r) (idF d) &&
    Nat.beq (pqK d H D.oh) (idF d) && commQ d X Y &&
    conjQ d H X (mulF2 d (pqK d X D.a) (pqK d Y D.c)) &&
    conjQ d H Y (mulF2 d (pqK d X D.b) (pqK d Y D.d)) &&
    distinctK ((List.range (D.r ^ 2)).map fun n => appBaseK d D.r [X, Y] n u)

end CFSG.KC.OpsF2K

end
