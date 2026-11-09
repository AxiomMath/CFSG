module

public import Certificates.Data.Kernel.SporSch.RootPair

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11

@[expose] noncomputable def twinQK (n w m nw nb N : Nat) (LR TR T QJ : Nat → Nat) (mm : Nat) :
    Bool :=
  strictB (Nat.mul (nat_lit 8) mm) (fun b8 =>
  allN (nat_lit 8) (fun k => strictB (QJ (Nat.add b8 k)) (fun j =>
    bIf(Nat.blt j N, eqAllK n (elF n w m nw nb LR TR j)
      (q8W (pg w m (T (Nat.mul (nat_lit 2) mm))) (pg w m (T (Nat.succ (Nat.mul (nat_lit 2) mm))))
        k), true))))

@[expose] noncomputable def subAK (n w m nw BP nb N nx zj : Nat)
    (LR TR X XI QJ QA QW QP : Nat → Nat) (mm : Nat) : Bool :=
  strictB (Nat.mul (nat_lit 8) mm) (fun b8 => strictB (Nat.mul (nat_lit 5) mm) (fun b5 =>
  bAnd(allN (nat_lit 8) (fun k => Nat.blt (QJ (Nat.add b8 k)) N),
  bAnd(Nat.beq (QJ (Nat.add b8 (nat_lit 1))) zj,
  bAnd(allN (nat_lit 8) (fun k => eqB w m BP nb (elF n w m nw nb LR TR (QJ (Nat.add b8 k)))
    (q8W (elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 2))))
      (elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 4)))) k)),
  bAnd(eqB w m BP nb (fun x => elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 4)))
      (elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 4))) x))
    (elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 1)))),
  bAnd(eqB w m BP nb (fun x => elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 2)))
      (elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 4)))
      (elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 2))) x)))
    (elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 4)))),
  bAnd(allN (nat_lit 5) (fun a => strictB (QA (Nat.add b5 a)) (fun t =>
    bAnd(Nat.ble (nat_lit 1) t, Nat.blt t nx))),
  allN (nat_lit 5) (fun a => allN (nat_lit 5) (fun b => bIf(Nat.blt a b,
    strictB (QA (Nat.add b5 a)) (fun ta => strictB (QA (Nat.add b5 b)) (fun tb =>
    strictB (Nat.add (Nat.mul (nat_lit 25) mm) (Nat.add (Nat.mul (nat_lit 5) a) b)) (fun u =>
    strictB (QW u) (fun k => strictB (QP u) (fun x => bAnd(Nat.blt k (nat_lit 8),
      bAnd(Nat.blt x n,
      strictB (pg w m (XI tb) (pg w m (X ta) (elF n w m nw nb LR TR (QJ (Nat.add b8 k))
          (pg w m (XI ta) (pg w m (X tb) x))))) (fun y =>
      allN (nat_lit 8) (fun k' => bIf(Nat.beq y (elF n w m nw nb LR TR (QJ (Nat.add b8 k')) x),
        false, true)))))))))), true)))))))))))

@[expose] noncomputable def pairQK (n w m nw BP nb : Nat) (LR TR RL CT PQ QJ : Nat → Nat)
    (nr nq d : Nat) : Bool :=
  bIf(Nat.beq (CT d) (nat_lit 0), strictB (RL d) (fun jx => strictB (Nat.mul d nr) (fun r =>
    allN nr (fun e => bIf(Nat.beq (CT e) (nat_lit 0), strictB (RL e) (fun jy =>
      bIf(eqB w m BP nb (fun x => elF n w m nw nb LR TR jx (elF n w m nw nb LR TR jy
          (elF n w m nw nb LR TR jx x))) (elF n w m nw nb LR TR jy),
        strictB (PQ (Nat.add r e)) (fun mm =>
          bAnd(Nat.blt mm nq, bAnd(inQ QJ mm jx, inQ QJ mm jy))),
        true)), true)))), true)

@[expose] noncomputable def rootTK (n w m nw BP nb : Nat) (LR TR RL RT CT IV : Nat → Nat)
    (d : Nat) : Bool :=
  bIf(Nat.beq (CT d) (nat_lit 0), strictB (IV d) (fun d' => bIf(Nat.blt d' d,
    bAnd(Nat.beq (CT d') (nat_lit 0),
    bAnd(eqAllK n (fun x => pg w m (RT d) (pg w m (RT d') x)) (fun x => x),
      eqB w m BP nb (fun x => elF n w m nw nb LR TR (RL d) (pg w m (RT d') x)) (fun x => x))),
    eqAllK n (elF n w m nw nb LR TR (RL d)) (pg w m (RT d)))), true)

@[expose] noncomputable def pairRK (w m w2 m2 BP nb : Nat) (RL RT CT PR QJ : Nat → Nat)
    (nr nq d : Nat) : Bool :=
  bIf(Nat.beq (CT d) (nat_lit 0), strictB (RT d) (fun X => strictB (PR d) (fun row =>
    strictB (RL d) (fun jd =>
    allN (Nat.sub nr (Nat.succ d)) (fun i => strictB (Nat.add (Nat.succ d) i) (fun e =>
      bIf(Nat.beq (CT e) (nat_lit 0),
        strictB (pg w2 m2 row e) (fun c => strictB (Nat.div c (nat_lit 64)) (fun mm =>
          bIf(bAnd(Nat.blt mm nq, bAnd(Nat.beq (QJ (Nat.div c (nat_lit 8))) jd,
              Nat.beq (QJ (Nat.add (Nat.mul (nat_lit 8) mm) (Nat.mod c (nat_lit 8)))) (RL e))),
            true,
            strictB (RT e) (fun Y =>
              bIf(eqB w m BP nb (fun x => pg w m X (pg w m Y (pg w m X x))) (pg w m Y),
                false, true))))),
        true)))))), true)

@[expose] noncomputable def q8Out (A B : Nat → Nat) (x y : Nat) : Bool :=
  strictB (A x) (fun a1 => strictB (A a1) (fun a2 => strictB (B x) (fun b0 =>
  strictB (A b0) (fun b1 => strictB (A b1) (fun b2 =>
  bAnd(bIf(Nat.beq y x, false, true), bAnd(bIf(Nat.beq y a2, false, true),
  bAnd(bIf(Nat.beq y a1, false, true), bAnd(bIf(Nat.beq y (A a2), false, true),
  bAnd(bIf(Nat.beq y b0, false, true), bAnd(bIf(Nat.beq y b2, false, true),
  bAnd(bIf(Nat.beq y b1, false, true), bIf(Nat.beq y (A b2), false, true)))))))))))))

@[expose] noncomputable def subRK (n w m nw BP nb N nr nx zj : Nat)
    (LR TR RL RT CT X XI QJ QR QA QW QP : Nat → Nat) (mm : Nat) : Bool :=
  strictB (Nat.mul (nat_lit 8) mm) (fun b8 => strictB (Nat.mul (nat_lit 5) mm) (fun b5 =>
  strictB (RT (QR (Nat.add b8 (nat_lit 2)))) (fun PA => strictB (RT (QR (Nat.add b8 (nat_lit 4))))
    (fun PB =>
  bAnd(allN (nat_lit 8) (fun k => Nat.blt (QJ (Nat.add b8 k)) N),
  bAnd(Nat.beq (QJ (Nat.add b8 (nat_lit 1))) zj,
  bAnd(allN (nat_lit 6) (fun i => strictB (Nat.add b8 (Nat.add (nat_lit 2) i)) (fun c =>
    strictB (QR c) (fun r => bAnd(Nat.blt r nr, bAnd(Nat.beq (CT r) (nat_lit 0),
      Nat.beq (RL r) (QJ c)))))),
  bAnd(allN (nat_lit 2) (fun k => eqB w m BP nb (elF n w m nw nb LR TR (QJ (Nat.add b8 k)))
    (q8W (pg w m PA) (pg w m PB) k)),
  bAnd(allN (nat_lit 6) (fun i => strictB (Nat.add (nat_lit 2) i) (fun k =>
    eqB w m BP nb (pg w m (RT (QR (Nat.add b8 k)))) (q8W (pg w m PA) (pg w m PB) k))),
  bAnd(eqB w m BP nb (fun x => pg w m PB (pg w m PB x)) (fun x => pg w m PA (pg w m PA x)),
  bAnd(eqB w m BP nb (fun x => pg w m PA (pg w m PB (pg w m PA x))) (pg w m PB),
  bAnd(allN (nat_lit 5) (fun a => strictB (QA (Nat.add b5 a)) (fun t =>
    bAnd(Nat.ble (nat_lit 1) t, Nat.blt t nx))),
  allN (nat_lit 5) (fun a => allN (nat_lit 5) (fun b => bIf(Nat.blt a b,
    strictB (QA (Nat.add b5 a)) (fun ta => strictB (QA (Nat.add b5 b)) (fun tb =>
    strictB (Nat.add (Nat.mul (nat_lit 25) mm) (Nat.add (Nat.mul (nat_lit 5) a) b)) (fun u =>
    strictB (QW u) (fun k => strictB (QP u) (fun x => bAnd(Nat.blt k (nat_lit 8),
      bAnd(Nat.blt x n,
      strictB (pg w m (XI tb) (pg w m (X ta) (q8W (pg w m PA) (pg w m PB) k
          (pg w m (XI ta) (pg w m (X tb) x))))) (fun y =>
      q8Out (pg w m PA) (pg w m PB) x y)))))))), true)))))))))))))))

end CFSG.KS.SporSch.MOC

end
