module

public import Certificates.Data.Kernel.Spor.MEnum

public section

namespace CFSG.KS.MEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.M11

@[expose] noncomputable def recPos (nw pm S c q x : Nat) : Nat :=
  nIf(Nat.beq (blk S nw pm q) x, q, c)

@[expose] noncomputable def clsOKQ (n w m nw pm A Ai B Bi mx cap R : Nat) (Bl : Nat)
    (qw qm P Lb QA QB QT : Nat) (S c : Nat) : Bool :=
  bAnd(Nat.ble c cap, bAnd(Nat.beq (ordC n w m R) mx,
  bAnd(Nat.beq (blk Bl nw pm (nat_lit 0)) R,
  bAnd(allN (Nat.sub c (nat_lit 1)) (fun k =>
      Nat.blt (blk S nw pm k) (blk S nw pm (Nat.succ k))),
  bAnd(allN c (fun k => strictB (blk S nw pm k) (fun x =>
      bAnd(Nat.blt (recPos nw pm S c (blk QA qw qm k) (conjK n w m A Ai x)) c,
        Nat.blt (recPos nw pm S c (blk QB qw qm k) (conjK n w m B Bi x)) c))),
  bAnd(allN c (fun k => bIf(Nat.beq k (nat_lit 0), true,
      strictB (blk P qw qm k) (fun p => strictB (blk Lb qw qm k) (fun l =>
        bAnd(Nat.blt p k, Nat.beq (blk Bl nw pm k) (nIf(Nat.beq l (nat_lit 0),
          conjK n w m A Ai (blk Bl nw pm p), conjK n w m B Bi (blk Bl nw pm p)))))))),
  Nat.beq (Nat.shiftRight
      (foldUp c (fun k M => strictN (recPos nw pm S c (blk QT qw qm k) (blk Bl nw pm k))
        (fun q => nIf(bAnd(Nat.blt q c, bIf(hasBit M q, false, true)),
          Nat.lor M (Nat.shiftLeft (nat_lit 1) q), Nat.lor M (Nat.shiftLeft (nat_lit 1) c))))
        (nat_lit 0)) c) (nat_lit 0)))))))

@[expose] noncomputable def clsOneQ (n w : Nat) (tA tB : List Nat) (mx cap qw : Nat)
    (QA QB QT : List Nat) (d : ClassDatum) : Bool :=
  strictB (mask w) (fun m => strictB (Nat.mul n w) (fun nw => strictB (mask nw) (fun pm =>
  strictB (mask qw) (fun qm => strictB (Nat.shiftLeft (nat_lit 1) qw) (fun qb =>
  strictB (packL w tA) (fun A => strictB (pinvS n w m A) (fun Ai =>
  strictB (packL w tB) (fun B => strictB (pinvS n w m B) (fun Bi =>
  Prod.rec (motive := fun _ => Bool) (fun _ d => Prod.rec (motive := fun _ => Bool) (fun _ d =>
  Prod.rec (motive := fun _ => Bool) (fun R d => Prod.rec (motive := fun _ => Bool) (fun Bl d =>
  Prod.rec (motive := fun _ => Bool) (fun P d => Prod.rec (motive := fun _ => Bool) (fun Lb S =>
    bAnd(allLtN (Nat.shiftLeft (nat_lit 1) nw) Bl, bAnd(allLtN (Nat.shiftLeft (nat_lit 1) nw) S,
    bAnd(allLtN qb P, bAnd(allLtN qb Lb, bAnd(allLtN qb QA, bAnd(allLtN qb QB,
    bAnd(allLtN qb QT,
      clsOKQ n w m nw pm A Ai B Bi mx cap R (packL nw Bl) qw qm (packL qw P) (packL qw Lb)
        (packL qw QA) (packL qw QB) (packL qw QT) (packL nw S) (lenN S))))))))) d) d) d)
    d) d) d)))))))))

end CFSG.KS.MEnum

end
