module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def siftKX (n w m nw : Nat) (LR TRI : Nat → Nat) (BP : Nat) (X : Nat → Nat)
    (nX : Nat) (f : Nat) : Nat → (Nat → Nat) → Bool :=
  Nat.rec (motive := fun _ => Nat → (Nat → Nat) → Bool)
    (fun _ g => allN nX (fun t => strictB (X t) (fun x => Nat.beq (g x) x)))
    (fun _ ih l g => strictB (LR l) (fun R =>
      strictB (rpos w m nw R (g (pg w m BP l))) (fun k =>
      bIf(Nat.blt k (rcnt R),
        strictB (TRI (Nat.add (roff n nw R) k)) (fun t => ih (Nat.succ l) (fun x => pg w m t (g x))),
        false))))
    f

@[expose] noncomputable def xPtsK(w m BP nb nD t : Nat) : Nat :=
  nIf(Nat.blt t nb, pg w m BP t, Nat.add (Nat.sub nD nb) t)

@[expose] noncomputable def agreeDK(nD w m : Nat) (PS PSI QS QSI : Nat → Nat) (kS : Nat) : Bool :=
  allN kS (fun j => allN nD (fun x => bAnd(Nat.beq (pg w m (PS j) x) (pg w m (QS j) x),
    Nat.beq (pg w m (PSI j) x) (pg w m (QSI j) x))))

@[expose] noncomputable def schKX (n w m nw : Nat) (S SI LR TR TRI : Nat → Nat)
    (kS BP nb i T h₀ cnt : Nat) (X : Nat → Nat) (nX : Nat) : Bool :=
  strictB (LR i) (fun R => strictB (rcnt R) (fun c => strictB (roff n nw R) (fun o =>
  allN cnt (fun dh => strictB (Nat.add h₀ dh) (fun h => bIf(Nat.blt h c,
    strictB (TR (Nat.add o h)) (fun th => strictB (rpt w m R h) (fun p =>
    allN (stCnt T) (fun j => strictB (letterK S SI kS (stAt T j)) (fun s =>
      strictB (rpos w m nw R (pg w m s p)) (fun k => bAnd(Nat.blt k c,
        strictB (TRI (Nat.add o k)) (fun ti =>
          siftKX n w m nw LR TRI BP X nX (Nat.sub nb (Nat.succ i)) (Nat.succ i)
            (fun x => pg w m ti (pg w m s (pg w m th x)))))))))),
    true))))))

end CFSG.KS.Raw

end
