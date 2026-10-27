module

public import Certificates.Data.Kernel.OpsF2KQ
public import Certificates.Data.Kernel.OpsF2KSq

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native
open CFSG.KC.Misc.G24 (mulF2)

@[expose] noncomputable def cubicQ (d A B : Nat) (D : CubData) : Bool :=
  let R := runQ d A B D.nregs D.prog
  let X := getR d R D.rx
  let Y := getR d R D.ry
  let H := getR d R D.rh
  let one := idF d
  let Z := commMQ d D.r X Y
  let u := pw2 D.t
  seedsOK d A B && decide (D.t < d) && D.prog.all expOK &&
    [D.r, D.oh, D.a, D.b, D.c, D.d, D.k, D.l, D.μ].all (decide <| · < 65536) &&
    decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && decide (D.rx < D.nregs) &&
    decide (D.ry < D.nregs) && decide (D.rh < D.nregs) && decide (0 < D.r) &&
    decide (0 < D.oh) && Nat.beq (pqK d X D.r) one && Nat.beq (pqK d Y D.r) one &&
    Nat.beq (pqK d H D.oh) one && !(Nat.beq (vmF d Z u) u) &&
    commQ d Z X && commQ d Z Y &&
    conjQ d H X (mulF2 d (mulF2 d (pqK d X D.a) (pqK d Y D.b)) (pqK d Z D.k)) &&
    conjQ d H Y (mulF2 d (mulF2 d (pqK d X D.c) (pqK d Y D.d)) (pqK d Z D.l)) &&
    conjQ d H Z (pqK d Z D.μ) &&
    distinctK ((List.range (D.r ^ 3)).map fun n => appBaseK d D.r [X, Y, Z] n u)

end CFSG.KC.OpsF2K

end
