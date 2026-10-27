module

public import Certificates.Data.Kernel.Misc.RuInv
public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.Misc.RuScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv

@[expose] noncomputable def yAp (ys : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun p _ ih => strictN ih (fun v => apP p v)) ys

@[expose] noncomputable def yPow (ys : List Nat) (j x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ ih => strictN ih (fun v => yAp ys v)) j

@[expose] noncomputable def wit0 (ys : List Nat) (b k : Nat) : Bool :=
  bAnd(Nat.beq (yPow ys k b) b,
    List.rec (motive := fun _ => Bool) true
      (fun e _ ih => bIf(Nat.beq (yPow ys (Nat.gcd k e) b) b, false, ih))
      [nat_lit 125, nat_lit 7, nat_lit 13, nat_lit 29])

@[expose] noncomputable def wit1 (ys : List Nat) (T j x x' : Nat) : Bool :=
  strictB (yPow ys j x) (fun p =>
    bAnd(Nat.beq (yPow ys j x') (apP T p),
      bIf(Nat.beq (apP T (yPow ys j (apP T x))) (yPow ys j (apP T x')), false, true)))

@[expose] noncomputable def witK (ys : List Nat) (T r : Nat) : Bool :=
  strictB (Nat.land r (nat_lit 3)) (fun c =>
    bIf(Nat.beq c (nat_lit 0), wit0 ys (fld(r, nat_lit 2, nat_lit 4095)) (fld(r, nat_lit 14, nat_lit 63)),
    bIf(Nat.beq c (nat_lit 1),
      wit1 ys T (fld(r, nat_lit 2, nat_lit 31)) (fld(r, nat_lit 7, nat_lit 4095))
        (fld(r, nat_lit 19, nat_lit 4095)),
      false)))

@[expose] noncomputable def chk2 (LR TR W : Nat → Nat) (H T lo cnt : Nat) : Bool :=
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 0)) (fun o0 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 1)) (fun o1 =>
  strictB (rcnt (LR 1)) (fun c1 =>
  allN cnt (fun d => strictB (Nat.add lo d) (fun i =>
    strictB (TR (Nat.add o0 (Nat.div i c1))) (fun t0 =>
    strictB (TR (Nat.add o1 (Nat.mod i c1))) (fun t1 =>
      witK [H, t0, t1] T (W i))))))))

@[expose] noncomputable def chk3 (LR TR W : Nat → Nat) (H T lo cnt : Nat) : Bool :=
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 0)) (fun o0 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 1)) (fun o1 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 2)) (fun o2 =>
  strictB (rcnt (LR 1)) (fun c1 =>
  strictB (rcnt (LR 2)) (fun c2 =>
  allN cnt (fun d => strictB (Nat.add lo d) (fun i =>
    strictB (Nat.div i c2) (fun q =>
    strictB (TR (Nat.add o0 (Nat.div q c1))) (fun t0 =>
    strictB (TR (Nat.add o1 (Nat.mod q c1))) (fun t1 =>
    strictB (TR (Nat.add o2 (Nat.mod i c2))) (fun t2 =>
      witK [H, t0, t1, t2] T (W i))))))))))))

end CFSG.KC.Misc.RuScan

end
