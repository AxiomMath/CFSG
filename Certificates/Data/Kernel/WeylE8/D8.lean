module

public import Certificates.Data.Kernel.WeylE8.Cent

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def swapKey (a b x : Nat) : Nat :=
  strictN (cf x a) fun fa => strictN (cf x b) fun fb =>
    Nat.add (Nat.sub (Nat.sub x (Nat.shiftLeft fa (Nat.mul (nat_lit 4) a)))
      (Nat.shiftLeft fb (Nat.mul (nat_lit 4) b)))
      (Nat.add (Nat.shiftLeft fb (Nat.mul (nat_lit 4) a)) (Nat.shiftLeft fa (Nat.mul (nat_lit 4) b)))

@[expose] noncomputable def swapRowOK (RK : Nat → Nat) (a b T : Nat) : Bool :=
  bAnd(Nat.blt a b, bAnd(Nat.blt b (nat_lit 8),
    allN (nat_lit 240) fun i => strictB (pg (nat_lit 8) (nat_lit 255) T i) fun e =>
      bAnd(Nat.blt e (nat_lit 240), Nat.beq (RK e) (swapKey a b (RK i)))))

@[expose] noncomputable def pa (DP p : Nat) : Nat := Nat.shiftRight (pg (nat_lit 8) (nat_lit 255) DP p) (nat_lit 3)

@[expose] noncomputable def pb (DP p : Nat) : Nat := Nat.land (pg (nat_lit 8) (nat_lit 255) DP p) (nat_lit 7)

@[expose] noncomputable def bindPairs (DP : Nat) (P : List (Nat × Nat)) : Bool :=
  bAnd(allN (nat_lit 27) (fun p => Nat.blt (pg (nat_lit 8) (nat_lit 255) DP p)
      (pg (nat_lit 8) (nat_lit 255) DP (Nat.succ p))),
    List.rec (motive := fun _ => Nat → Bool) (fun p => Nat.beq p (nat_lit 28))
      (fun ab _ ih p => bAnd(Nat.blt ab.1 (nat_lit 8), bAnd(Nat.blt ab.2 (nat_lit 8),
        bAnd(Nat.beq ab.1 (pa DP p), bAnd(Nat.beq ab.2 (pb DP p), ih (Nat.succ p)))))) P (nat_lit 0))

@[expose] noncomputable def evenB (m : Nat) : Bool := Nat.beq (Nat.land (pop8 m) (nat_lit 1)) (nat_lit 0)

@[expose] noncomputable def d1K (ST : Nat → Nat) : Bool :=
  allN (nat_lit 240) fun r => bIf(Nat.blt r (nat_lit 112), true,
    allN (nat_lit 256) fun m => bIf(bAnd(evenB m, Nat.blt (nat_lit 0) m),
      notB' (Nat.beq (pg (nat_lit 8) (nat_lit 255) (ST m) r) r), true))

@[expose] noncomputable def memK (ST : Nat → Nat) (X : Nat) : Bool :=
  strictB (pg (nat_lit 8) (nat_lit 255) X (nat_lit 112)) fun v =>
    strictB (Nat.mul (nat_lit 2) (Nat.sub v (nat_lit 112))) fun j2 =>
      bAnd(Nat.ble (nat_lit 112) v,
        bIf(bAnd(evenB j2, Nat.beq X (Nat.land (ST j2) (mask (nat_lit 1920)))), true,
          bAnd(evenB (Nat.succ j2), Nat.beq X (Nat.land (ST (Nat.succ j2)) (mask (nat_lit 1920))))))

@[expose] noncomputable def d2K (RT ST : Nat → Nat) : Bool :=
  strictB (RT (nat_lit 1)) fun R1 => allN (nat_lit 240) fun r =>
    strictB (pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) R1 (RT r)) fun X =>
      Bool.rec (motive := fun _ => Bool) (notB' (Nat.blt r (nat_lit 4))) (Nat.blt r (nat_lit 4))
        (memK ST X)

@[expose] noncomputable def swapMask (a b m : Nat) : Nat :=
  strictN (Nat.land (Nat.shiftRight m a) (nat_lit 1)) fun ba =>
    strictN (Nat.land (Nat.shiftRight m b) (nat_lit 1)) fun bb =>
      Nat.add (Nat.sub (Nat.sub m (Nat.shiftLeft ba a)) (Nat.shiftLeft bb b))
        (Nat.add (Nat.shiftLeft bb a) (Nat.shiftLeft ba b))

@[expose] noncomputable def d3At (RT ST : Nat → Nat) (DP p : Nat) : Bool :=
  allN (nat_lit 2) fun s =>
    strictB (RT (Nat.add (Nat.mul (nat_lit 4) p) s)) fun R =>
      allN (nat_lit 7) fun k => strictB (Nat.add (nat_lit 1) (Nat.shiftLeft (nat_lit 2) k)) fun m =>
        Nat.beq (pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255)
            (pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) R (ST m)) R)
          (Nat.land (ST (swapMask (pa DP p) (pb DP p) m)) (mask (nat_lit 1920)))

@[expose] noncomputable def d5K (RK RT PT : Nat → Nat) (DP : Nat) : Bool :=
  allN (nat_lit 28) fun p => bAnd(swapRowOK RK (pa DP p) (pb DP p) (PT p),
    Nat.beq (PT p) (RT (Nat.add (Nat.mul (nat_lit 4) p) (nat_lit 1))))

end CFSG.KLC.E8

end
