module

public import Certificates.Data.Kernel.Misc.RuScan

public section

namespace CFSG.KC.Misc.RuScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv

@[expose] noncomputable def leafOK (ys : List Nat) (T : Nat) (K V : Nat → Nat) (l p : Nat) :
    Bool :=
  strictB (V (Nat.add (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) l)) (nat_lit 28))) (fun q =>
  strictB (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) l)) (fun vo =>
  strictB (Nat.mul (nat_lit 32) p) (fun ko =>
  bAnd(Nat.ble (nat_lit 1) q, bAnd(Nat.ble q (nat_lit 7),
    allN (nat_lit 4) (fun b => allN q (fun i =>
      strictB (K (Nat.add ko (Nat.add (Nat.mul (nat_lit 4) i) b))) (fun x =>
      bAnd(Nat.beq (yAp ys x)
          (nIf(Nat.beq i (nat_lit 0), b,
            K (Nat.add ko (Nat.add (Nat.mul (nat_lit 4) (Nat.sub i (nat_lit 1))) b)))),
        Nat.beq (yPow ys (Nat.succ i) (apP T x))
          (nIf(Nat.beq (Nat.succ i) q, apP T b,
            V (Nat.add vo (Nat.add (Nat.mul (nat_lit 4) i) b)))))))))))))

@[expose] noncomputable def leafStep (ys : List Nat) (T : Nat) (K V : Nat → Nat) (r s : Nat) :
    Nat :=
  nIf(Nat.beq s (nat_lit 0), nat_lit 0,
    nIf(Nat.beq (Nat.land r (nat_lit 3)) (nat_lit 2),
      nIf(Nat.ble (nat_lit 2) s,
        nIf(leafOK ys T K V (Nat.shiftRight r (nat_lit 2)) (Nat.sub s (nat_lit 2)),
          Nat.sub s (nat_lit 1), nat_lit 0),
        nat_lit 0),
      s))

@[expose] noncomputable def chkL2 (LR TR W K V : Nat → Nat) (H T lo cnt s1 s0 : Nat) : Bool :=
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 0)) (fun o0 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 1)) (fun o1 =>
  strictB (rcnt (LR 1)) (fun c1 =>
  Nat.beq (foldN cnt (fun d s => strictN (Nat.add lo d) (fun i =>
      strictN (W i) (fun r =>
      nIf(Nat.beq (Nat.land r (nat_lit 3)) (nat_lit 2),
        strictN (TR (Nat.add o0 (Nat.div i c1))) (fun t0 =>
        strictN (TR (Nat.add o1 (Nat.mod i c1))) (fun t1 =>
          leafStep [H, t0, t1] T K V r s)),
        s))))
    (Nat.succ s1)) (Nat.succ s0))))

@[expose] noncomputable def chkL3 (LR TR W K V : Nat → Nat) (H T lo cnt s1 s0 : Nat) : Bool :=
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 0)) (fun o0 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 1)) (fun o1 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 2)) (fun o2 =>
  strictB (rcnt (LR 1)) (fun c1 =>
  strictB (rcnt (LR 2)) (fun c2 =>
  Nat.beq (foldN cnt (fun d s => strictN (Nat.add lo d) (fun i =>
      strictN (W i) (fun r =>
      nIf(Nat.beq (Nat.land r (nat_lit 3)) (nat_lit 2),
        strictN (Nat.div i c2) (fun q =>
        strictN (TR (Nat.add o0 (Nat.div q c1))) (fun t0 =>
        strictN (TR (Nat.add o1 (Nat.mod q c1))) (fun t1 =>
        strictN (TR (Nat.add o2 (Nat.mod i c2))) (fun t2 =>
          leafStep [H, t0, t1, t2] T K V r s)))),
        s))))
    (Nat.succ s1)) (Nat.succ s0))))))

end CFSG.KC.Misc.RuScan

end
