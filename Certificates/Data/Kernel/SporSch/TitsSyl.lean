module

public import Certificates.Data.Kernel.SporSch.TitsCnt
public import Certificates.Data.Kernel.PkPow

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.PkPow

@[expose] noncomputable def cube1 (n w X : Nat) : Bool :=
  Nat.beq (pcomp n w (mask w) X (pcomp n w (mask w) X X)) (pidn n w)

@[expose] noncomputable def rel3 (n w X Y Z : Nat) : Bool :=
  strictB (pcomp n w (mask w) Y Z) (fun yz => strictB (pcomp n w (mask w) Z Y) (fun zy =>
    bAnd(cube1 n w X, bAnd(cube1 n w Y, bAnd(cube1 n w Z,
    bAnd(Nat.beq (pcomp n w (mask w) X Y) (pcomp n w (mask w) Y X),
    bAnd(Nat.beq (pcomp n w (mask w) X Z) (pcomp n w (mask w) Z X),
    bAnd(bIf(Nat.beq yz (pcomp n w (mask w) X zy), true,
      Nat.beq yz (pcomp n w (mask w) (pcomp n w (mask w) X X) zy)),
      bIf(Nat.beq yz zy, false, true)))))))))

@[expose] noncomputable def p513 (c : Nat) : Bool :=
  bAnd(bIf(Nat.beq (Nat.mod c (nat_lit 5)) (nat_lit 0), false, true),
    bIf(Nat.beq (Nat.mod c (nat_lit 13)) (nat_lit 0), false, true))

@[expose] noncomputable def lines3 (n w X Y Z : Nat) : Bool :=
  bAnd(p513 (nfix n w X), bAnd(p513 (nfix n w (pcomp n w (mask w) Y Z)),
    p513 (nfix n w (pcomp n w (mask w) Y (pcomp n w (mask w) Z Z)))))

@[expose] noncomputable def baseEqF (BP nb : Nat) (gx gy : Nat → Nat) : Bool :=
  allN nb (fun t => strictB (pg 11 (mask 11) BP t) (fun b => Nat.beq (gx b) (gy b)))

@[expose] noncomputable def invTB (BP T B t0 t1 t2 t3 t4 : Nat) : Bool :=
  bIf(bAnd(baseComm BP 5 (gptR t0 t1 t2 t3 t4) (pgR T),
      bAnd(baseComm BP 5 (gptR t0 t1 t2 t3 t4) (pgR B),
        baseEqF BP 5 (fun i => gptR t0 t1 t2 t3 t4 (gptR t0 t1 t2 t3 t4 i)) (fun i => i))),
    bIf(baseEqF BP 5 (gptR t0 t1 t2 t3 t4) (fun i => i), true,
      baseEqF BP 5 (gptR t0 t1 t2 t3 t4) (pgR T)),
    true)

end CFSG.KS.SporSch

end
