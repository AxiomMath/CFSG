module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def invTabK (kS T : Nat) : Bool :=
  strictB (Nat.shiftRight (stCnt T) (nat_lit 1)) (fun q => bAnd(Nat.beq (stCnt T) (Nat.add q q),
    allN q (fun j => strictB (stAt T j) (fun l =>
      bAnd(Nat.blt l kS, Nat.beq (stAt T (Nat.add q j)) (Nat.add kS l))))))

@[expose] noncomputable def utabF (n w m nw : Nat) (LR TR U : Nat → Nat) (i D : Nat) : Bool :=
  strictB (LR (Nat.succ i)) (fun R1 => strictB (LR (Nat.succ (Nat.succ i))) (fun R2 =>
  strictB (roff n nw R1) (fun o1 => strictB (roff n nw R2) (fun o2 =>
  allN (rcnt R1) (fun a => allN (rcnt R2) (fun b =>
    Nat.beq (U (Nat.add (Nat.mul a D) b))
      (pcomp n w m (TR (Nat.add o1 a)) (TR (Nat.add o2 b)))))))))

@[expose] noncomputable def vtabK (n w m nw idn : Nat) (LR TRI : Nat → Nat) (BP i : Nat) : Bool :=
  strictB (LR (Nat.succ i)) (fun R1 => strictB (LR (Nat.succ (Nat.succ i))) (fun R2 =>
  strictB (roff n nw R1) (fun o1 => strictB (roff n nw R2) (fun o2 =>
  allN (rcnt R1) (fun a => allN (rcnt R2) (fun b =>
    siftK n w m nw idn LR TRI BP (nat_lit 2) (Nat.succ i)
      (pcomp n w m (TRI (Nat.add o2 b)) (TRI (Nat.add o1 a)))))))))

@[expose] noncomputable def t3K (n w m nw : Nat) (S SI LR TR TRI U : Nat → Nat)
    (kS BP i T D h j : Nat) : Bool :=
  strictB (LR i) (fun R => strictB (roff n nw R) (fun o =>
  strictB (TR (Nat.add o h)) (fun th =>
  strictB (letterK S SI kS (stAt T j)) (fun s =>
  strictB (rpos w m nw R (pg w m s (rpt w m R h))) (fun k => bAnd(Nat.blt k (rcnt R),
  strictB (TRI (Nat.add o k)) (fun ti =>
  strictB (rpos w m nw (LR (Nat.succ i))
      (pg w m ti (pg w m s (pg w m th (pg w m BP (Nat.succ i)))))) (fun k1 =>
  bAnd(Nat.blt k1 (rcnt (LR (Nat.succ i))),
  strictB (rpos w m nw (LR (Nat.succ (Nat.succ i)))
      (pg w m (TRI (Nat.add (roff n nw (LR (Nat.succ i))) k1))
        (pg w m ti (pg w m s (pg w m th (pg w m BP (Nat.succ (Nat.succ i)))))))) (fun k2 =>
  bAnd(Nat.blt k2 (rcnt (LR (Nat.succ (Nat.succ i)))),
    Nat.beq (pcomp n w m s th)
      (pcomp n w m (TR (Nat.add o k)) (U (Nat.add (Nat.mul k1 D) k2))))))))))))))

@[expose] noncomputable def sch3F (n w m nw : Nat) (S SI LR TR TRI U : Nat → Nat)
    (kS BP i T D h₀ cnt : Nat) : Bool :=
  strictB (rcnt (LR i)) (fun c => strictB (Nat.shiftRight (stCnt T) (nat_lit 1)) (fun q =>
  allN cnt (fun dh => strictB (Nat.add h₀ dh) (fun h => bIf(Nat.blt h c,
    allN q (fun j => t3K n w m nw S SI LR TR TRI U kS BP i T D h j), true)))))

end CFSG.KS.Raw

end
