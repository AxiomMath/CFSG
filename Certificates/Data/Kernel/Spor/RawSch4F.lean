module

public import Certificates.Data.Kernel.Spor.RawSch3F

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def ix4 (E D a b c : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.add (Nat.mul a E) b) D) c

@[expose] noncomputable def utab4F (n w m nw : Nat) (LR TR U : Nat → Nat) (i E D : Nat) : Bool :=
  strictB (LR (Nat.succ i)) (fun R1 => strictB (LR (Nat.succ (Nat.succ i))) (fun R2 =>
  strictB (LR (Nat.succ (Nat.succ (Nat.succ i)))) (fun R3 =>
  strictB (roff n nw R1) (fun o1 => strictB (roff n nw R2) (fun o2 =>
  strictB (roff n nw R3) (fun o3 =>
  allN (rcnt R2) (fun b => allN (rcnt R3) (fun c =>
  strictB (pcomp n w m (TR (Nat.add o2 b)) (TR (Nat.add o3 c))) (fun P =>
  allN (rcnt R1) (fun a =>
    Nat.beq (U (ix4 E D a b c)) (pcomp n w m (TR (Nat.add o1 a)) P)))))))))))

@[expose] noncomputable def vtab4K (n w m nw idn : Nat) (LR TRI U : Nat → Nat) (BP i E D : Nat) :
    Bool :=
  strictB (LR (Nat.succ i)) (fun R1 => strictB (LR (Nat.succ (Nat.succ i))) (fun R2 =>
  strictB (LR (Nat.succ (Nat.succ (Nat.succ i)))) (fun R3 =>
  strictB (roff n nw R1) (fun o1 => strictB (roff n nw R2) (fun o2 =>
  strictB (roff n nw R3) (fun o3 =>
  allN (rcnt R1) (fun a => allN (rcnt R2) (fun b => allN (rcnt R3) (fun c =>
  strictB (rpos w m nw R1 (pg w m (TRI (Nat.add o3 c)) (pg w m (TRI (Nat.add o2 b))
      (pg w m (TRI (Nat.add o1 a)) (pg w m BP (Nat.succ i)))))) (fun k1 =>
  bAnd(Nat.blt k1 (rcnt R1),
  strictB (rpos w m nw R2 (pg w m (TRI (Nat.add o1 k1)) (pg w m (TRI (Nat.add o3 c))
      (pg w m (TRI (Nat.add o2 b)) (pg w m (TRI (Nat.add o1 a))
        (pg w m BP (Nat.succ (Nat.succ i)))))))) (fun k2 =>
  bAnd(Nat.blt k2 (rcnt R2),
  strictB (rpos w m nw R3 (pg w m (TRI (Nat.add o2 k2)) (pg w m (TRI (Nat.add o1 k1))
      (pg w m (TRI (Nat.add o3 c)) (pg w m (TRI (Nat.add o2 b)) (pg w m (TRI (Nat.add o1 a))
        (pg w m BP (Nat.succ (Nat.succ (Nat.succ i)))))))))) (fun k3 =>
  bAnd(Nat.blt k3 (rcnt R3),
    Nat.beq (pcomp n w m (U (ix4 E D a b c)) (U (ix4 E D k1 k2 k3))) idn)))))))))))))))

@[expose] noncomputable def t4K (n w m nw : Nat) (S SI LR TR TRI U : Nat → Nat)
    (kS BP i T E D h j : Nat) : Bool :=
  strictB (LR i) (fun R => strictB (roff n nw R) (fun o =>
  strictB (TR (Nat.add o h)) (fun th =>
  strictB (letterK S SI kS (stAt T j)) (fun s =>
  strictB (rpos w m nw R (pg w m s (rpt w m R h))) (fun k => bAnd(Nat.blt k (rcnt R),
  strictB (TRI (Nat.add o k)) (fun ti =>
  strictB (LR (Nat.succ i)) (fun R1 => strictB (LR (Nat.succ (Nat.succ i))) (fun R2 =>
  strictB (LR (Nat.succ (Nat.succ (Nat.succ i)))) (fun R3 =>
  strictB (rpos w m nw R1 (pg w m ti (pg w m s (pg w m th (pg w m BP (Nat.succ i)))))) (fun k1 =>
  bAnd(Nat.blt k1 (rcnt R1),
  strictB (TRI (Nat.add (roff n nw R1) k1)) (fun t1 =>
  strictB (rpos w m nw R2
      (pg w m t1 (pg w m ti (pg w m s (pg w m th (pg w m BP (Nat.succ (Nat.succ i)))))))) (fun k2 =>
  bAnd(Nat.blt k2 (rcnt R2),
  strictB (rpos w m nw R3 (pg w m (TRI (Nat.add (roff n nw R2) k2))
      (pg w m t1 (pg w m ti (pg w m s (pg w m th
        (pg w m BP (Nat.succ (Nat.succ (Nat.succ i)))))))))) (fun k3 =>
  bAnd(Nat.blt k3 (rcnt R3),
    Nat.beq (pcomp n w m s th)
      (pcomp n w m (TR (Nat.add o k)) (U (ix4 E D k1 k2 k3))))))))))))))))))))

@[expose] noncomputable def sch4F (n w m nw : Nat) (S SI LR TR TRI U : Nat → Nat)
    (kS BP i T E D h₀ cnt : Nat) : Bool :=
  strictB (rcnt (LR i)) (fun c => strictB (Nat.shiftRight (stCnt T) (nat_lit 1)) (fun q =>
  allN cnt (fun dh => strictB (Nat.add h₀ dh) (fun h => bIf(Nat.blt h c,
    allN q (fun j => t4K n w m nw S SI LR TR TRI U kS BP i T E D h j), true)))))

end CFSG.KS.Raw

end
