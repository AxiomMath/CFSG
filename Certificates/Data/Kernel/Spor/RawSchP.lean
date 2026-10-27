module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def schWalkK (n w m nw : Nat) (LR TR TRI : Nat → Nat) (BP P : Nat) (f : Nat) :
    Nat → (Nat → Nat) → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → (Nat → Nat) → Nat → Bool)
    (fun _ _ Q => bAnd(szOK n w, Nat.beq P Q))
    (fun _ ih l ev Q => strictB (LR l) (fun R => strictB (pg w m BP l) (fun b =>
      bAnd(Nat.blt b n, strictB (rpos w m nw R (ev (pg w m P b))) (fun k =>
      bIf(Nat.blt k (rcnt R),
        strictB (Nat.add (roff n nw R) k) (fun t => strictB (TRI t) (fun ti =>
          strictB (pcomp n w m Q (TR t)) (fun Q' =>
            ih (Nat.succ l) (fun x => pg w m ti (ev x)) Q'))),
        false))))))
    f

@[expose] noncomputable def schK2 (n w m nw : Nat) (S SI LR TR TRI : Nat → Nat)
    (kS BP nb i T h₀ cnt : Nat) : Bool :=
  strictB (LR i) (fun R => strictB (rcnt R) (fun c => strictB (roff n nw R) (fun o =>
  allN cnt (fun dh => strictB (Nat.add h₀ dh) (fun h => bIf(Nat.blt h c,
    strictB (TR (Nat.add o h)) (fun th => strictB (rpt w m R h) (fun p =>
    allN (stCnt T) (fun j => strictB (letterK S SI kS (stAt T j)) (fun s =>
      strictB (rpos w m nw R (pg w m s p)) (fun k => bAnd(Nat.blt k c,
        strictB (pcomp n w m s th) (fun P => strictB (Nat.add o k) (fun t =>
        strictB (TRI t) (fun ti =>
          schWalkK n w m nw LR TR TRI BP P (Nat.sub nb (Nat.succ i)) (Nat.succ i)
            (fun x => pg w m ti x) (TR t)))))))))),
    true))))))

end CFSG.KS.Raw

end
