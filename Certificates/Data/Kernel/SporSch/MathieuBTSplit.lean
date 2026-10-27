module

public import Certificates.Data.Kernel.SporSch.MathieuBT

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def btBr (n w m nw BP : Nat) (LR TR TRI : Nat → Nat) (X Y k t : Nat) :
    Nat :=
  strictN (LR (nat_lit 0)) (fun R => strictN (pg w m BP (nat_lit 0)) (fun b =>
    strictN (roff n nw R) (fun o => strictN (walkK w m X b n b (nat_lit 0)) (fun lb =>
    strictN (pg w m (pidn n w) (rpt w m R t)) (fun q =>
      nIf(Nat.beq (walkK w m Y q n q (nat_lit 0)) lb,
        btGo n w m nw BP LR TR TRI X Y k (nat_lit 1) (pcomp n w m (pidn n w) (TR (Nat.add o t)))
          (pcomp n w m (TRI (Nat.add o t)) (pidn n w)) (nat_lit 0), nat_lit 0))))))

@[expose] noncomputable def btR (n w m nw BP : Nat) (LR TR TRI : Nat → Nat) (X Y k lo len : Nat) :
    Nat :=
  foldBlk lo (fun t s => Nat.add s (btBr n w m nw BP LR TR TRI X Y k t)) len (nat_lit 0)

end CFSG.KS.SporSch.MBT

end
