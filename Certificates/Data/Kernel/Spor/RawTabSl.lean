module

public import Certificates.Data.Kernel.Spor.RawSch4F

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def utRowF (n w m nw : Nat) (LR TR U : Nat → Nat) (i D a : Nat) : Bool :=
  bIf(Nat.blt a (rcnt (LR (Nat.succ i))),
  strictB (LR (Nat.succ i)) (fun R1 => strictB (LR (Nat.succ (Nat.succ i))) (fun R2 =>
  strictB (roff n nw R1) (fun o1 => strictB (roff n nw R2) (fun o2 =>
  allN (rcnt R2) (fun b =>
    Nat.beq (U (Nat.add (Nat.mul a D) b))
      (pcomp n w m (TR (Nat.add o1 a)) (TR (Nat.add o2 b)))))))), true)

@[expose] noncomputable def utSlF (n w m nw : Nat) (LR TR U : Nat → Nat) (i D lo len : Nat) :
    Bool :=
  allN len (fun d => utRowF n w m nw LR TR U i D (Nat.add lo d))

@[expose] noncomputable def ut4RowF (n w m nw : Nat) (LR TR U : Nat → Nat) (i E D b : Nat) :
    Bool :=
  bIf(Nat.blt b (rcnt (LR (Nat.succ (Nat.succ i)))),
  strictB (LR (Nat.succ i)) (fun R1 =>
  strictB (LR (Nat.succ (Nat.succ (Nat.succ i)))) (fun R3 =>
  strictB (roff n nw R1) (fun o1 => strictB (roff n nw (LR (Nat.succ (Nat.succ i)))) (fun o2 =>
  strictB (roff n nw R3) (fun o3 =>
  allN (rcnt R3) (fun c =>
  strictB (pcomp n w m (TR (Nat.add o2 b)) (TR (Nat.add o3 c))) (fun P =>
  allN (rcnt R1) (fun a =>
    Nat.beq (U (ix4 E D a b c)) (pcomp n w m (TR (Nat.add o1 a)) P))))))))), true)

@[expose] noncomputable def ut4SlF (n w m nw : Nat) (LR TR U : Nat → Nat) (i E D lo len : Nat) :
    Bool :=
  allN len (fun d => ut4RowF n w m nw LR TR U i E D (Nat.add lo d))

@[expose] noncomputable def vt4RowF (n w m nw idn : Nat) (LR TRI U : Nat → Nat)
    (BP i E D a : Nat) : Bool :=
  bIf(Nat.blt a (rcnt (LR (Nat.succ i))),
  strictB (LR (Nat.succ i)) (fun R1 => strictB (LR (Nat.succ (Nat.succ i))) (fun R2 =>
  strictB (LR (Nat.succ (Nat.succ (Nat.succ i)))) (fun R3 =>
  strictB (roff n nw R1) (fun o1 => strictB (roff n nw R2) (fun o2 =>
  strictB (roff n nw R3) (fun o3 =>
  allN (rcnt R2) (fun b => allN (rcnt R3) (fun c =>
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
    Nat.beq (pcomp n w m (U (ix4 E D a b c)) (U (ix4 E D k1 k2 k3))) idn)))))))))))))), true)

@[expose] noncomputable def vt4SlF (n w m nw idn : Nat) (LR TRI U : Nat → Nat)
    (BP i E D lo len : Nat) : Bool :=
  allN len (fun d => vt4RowF n w m nw idn LR TRI U BP i E D (Nat.add lo d))

end CFSG.KS.Raw

end
