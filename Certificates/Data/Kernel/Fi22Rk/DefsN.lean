module

public import Certificates.Data.Kernel.Fi22Rk.Defs

public section

namespace CFSG.KC.Fi22Rk

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim
open CFSG.KLie.CT (orB notB anyN sumN)

@[expose] noncomputable def pbRunKN (N : Nat) (MUK LK EK PLK SL : Nat → Nat) : Bool :=
  bAnd(Nat.beq (LK (nat_lit 0)) (pidn (nat_lit 243) (nat_lit 8)), bAnd(Nat.beq (PLK (nat_lit 0)) (nat_lit 0),
  bAnd(allN N (fun k => strictB (LK k) fun p =>
    permOK (nat_lit 243) (nat_lit 8) (nat_lit 255) (nat_lit 1944) p
      (pinvS (nat_lit 243) (nat_lit 8) (nat_lit 255) p)),
  bAnd(CFSG.KC.BfsPin.distinctK N LK SL,
    Nat.beq (pbRun MUK LK EK PLK N) N))))

@[expose] noncomputable def mtKN (N : Nat) (LK MTK : Nat → Nat) : Bool :=
  allN N fun k => allN N fun l => strictB (mt MTK k l) fun j =>
    bAnd(Nat.blt j N, Nat.beq (LK j) (ps (LK k) (LK l)))

@[expose] noncomputable def treeKN (N : Nat) (MUK LK PLK MTK FMK : Nat → Nat) : Bool :=
  bAnd(allN N (fun k => orB (Nat.beq k (nat_lit 0))
    (strictB (parP PLK k) fun p => strictB (labP PLK k) fun b =>
      bAnd(Nat.blt p k, bAnd(Nat.blt b (nat_lit 2), Nat.beq (LK k) (ps (LK p) (MUK b)))))),
  bAnd(allN (nat_lit 2) (fun l => anyN N fun r => Nat.beq (MUK l) (LK r)),
  bAnd(allN N (fun k => anyN N fun r => Nat.beq (mt MTK k r) (nat_lit 0)),
    allN N fun k => strictB (LK k) fun p => strictB (FMK k) fun f =>
      bAnd(Nat.beq (Nat.shiftRight f (nat_lit 243)) (nat_lit 0),
        allN (nat_lit 243) fun v => Nat.beq fld(f, v, nat_lit 1)
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
            (Nat.beq (pg (nat_lit 8) (nat_lit 255) p v) v))))))

@[expose] noncomputable def fixAtN (N : Nat) (MTK FMK : Nat → Nat) (k : Nat) : Bool :=
  strictB (FMK k) fun fk => bAnd(orB (Nat.beq k (nat_lit 0)) (Nat.ble (pop fk) (nat_lit 27)),
    allN N fun l => orB (exK MTK k l) (strictB (Nat.land fk (FMK l)) fun f2 =>
      bAnd(Nat.ble (pop f2) (nat_lit 9),
        allN N fun r => orB (notB (cm MTK k r)) (orB (notB (cm MTK l r))
          (orB (anyN (nat_lit 3) fun i => anyN (nat_lit 3) fun j =>
              Nat.beq r (mt MTK (pwI MTK k i) (pwI MTK l j)))
            (Nat.ble (pop (Nat.land f2 (FMK r))) (nat_lit 3)))))))

end CFSG.KC.Fi22Rk

end
