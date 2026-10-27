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

end CFSG.KS.SporSch.MOC

end
