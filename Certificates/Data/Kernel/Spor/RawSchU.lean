module

public import Certificates.Data.Kernel.Spor.RawSchP

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def schWalkU (n w m nw : Nat) (LR TR TRI U : Nat → Nat) (BP D P : Nat)
    (f : Nat) : Nat → (Nat → Nat) → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → (Nat → Nat) → Nat → Bool)
    (fun l ev Q => strictB (LR l) (fun R => strictB (pg w m BP l) (fun b =>
      bAnd(Nat.blt b n, strictB (rpos w m nw R (ev (pg w m P b))) (fun k =>
      bAnd(Nat.blt k (rcnt R), strictB (TRI (Nat.add (roff n nw R) k)) (fun ti =>
      strictB (LR (Nat.succ l)) (fun R2 => strictB (pg w m BP (Nat.succ l)) (fun b2 =>
      bAnd(Nat.blt b2 n, strictB (rpos w m nw R2 (pg w m ti (ev (pg w m P b2)))) (fun k2 =>
      bAnd(Nat.blt k2 (rcnt R2), bAnd(szOK n w,
        Nat.beq P (pcomp n w m Q (U (Nat.add (Nat.mul k D) k2))))))))))))))))
    (fun _ ih l ev Q => strictB (LR l) (fun R => strictB (pg w m BP l) (fun b =>
      bAnd(Nat.blt b n, strictB (rpos w m nw R (ev (pg w m P b))) (fun k =>
      bIf(Nat.blt k (rcnt R),
        strictB (Nat.add (roff n nw R) k) (fun t => strictB (TRI t) (fun ti =>
          strictB (pcomp n w m Q (TR t)) (fun Q' =>
            ih (Nat.succ l) (fun x => pg w m ti (ev x)) Q'))),
        false))))))
    f

@[expose] noncomputable def schK2U (n w m nw : Nat) (S SI LR TR TRI U : Nat → Nat)
    (kS BP D nb i T h₀ cnt : Nat) : Bool :=
  strictB T (fun T =>
  strictB (LR i) (fun R => strictB (rcnt R) (fun c => strictB (roff n nw R) (fun o =>
  allN cnt (fun dh => strictB (Nat.add h₀ dh) (fun h => bIf(Nat.blt h c,
    strictB (TR (Nat.add o h)) (fun th => strictB (rpt w m R h) (fun p =>
    allN (stCnt T) (fun j => strictB (letterK S SI kS (stAt T j)) (fun s =>
      strictB (rpos w m nw R (pg w m s p)) (fun k => bAnd(Nat.blt k c,
        strictB (pcomp n w m s th) (fun P => strictB (Nat.add o k) (fun t =>
        strictB (TRI t) (fun ti =>
          schWalkU n w m nw LR TR TRI U BP D P
            (Nat.sub nb (Nat.succ (Nat.succ (Nat.succ i)))) (Nat.succ i)
            (fun x => pg w m ti x) (TR t)))))))))),
    true)))))))

end CFSG.KS.Raw

end
