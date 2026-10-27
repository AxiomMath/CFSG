module

public import Certificates.Data.Kernel.Fi22S0.Check
public import Certificates.Data.Kernel.Fi22S0.Kill
public import Certificates.Data.Kernel.Fi22.Letters

public section

namespace CFSG.KC.Fi22Cls

open CFSG.KC.Enum CFSG.KC.Fi22S0 CFSG.KS.Fi22L

@[expose] noncomputable def letT (P S l : Nat) : Nat :=
  nIf(Nat.beq (Nat.land l (nat_lit 1)) (nat_lit 0), regT P (wrOf S (Nat.shiftRight l (nat_lit 1))),
    tabK P (Nat.add (nat_lit 134) (Nat.shiftRight l (nat_lit 1))))

@[expose] noncomputable def wordK (L w : Nat → Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ K => K)
    (fun _ ih s K => strictN (ih (Nat.succ s) K) fun K' => strictN (L (w s)) fun T => mapK T K')

@[expose] noncomputable def eK (g pp pj : Nat → Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ K => K)
    (fun _ ih i K => nIf(Nat.beq i (nat_lit 0), K,
      strictN (pp i) fun p => strictN (ih p K) fun K' => strictN (g (pj i)) fun T => mapK T K'))

@[expose] noncomputable def conjC (rep cls wo wd L glob key g pp pj : Nat → Nat) (k0 n l : Nat) :
    Bool :=
  strictB (rep l) fun r => strictB (cls l) fun k => strictB (wo l) fun s =>
    strictB (wo (Nat.succ l)) fun e => strictB (glob k) fun ρ =>
      bAnd(Nat.blt r n, bAnd(Nat.blt k (nat_lit 4), bAnd(Nat.ble s e,
        bAnd(allBlk s (fun t => Nat.blt (wd t) (nat_lit 32)) (Nat.sub e s),
          Nat.beq (wordK L wd (Nat.sub e s) s (key r))
            (eK g pp pj (Nat.succ ρ) ρ (wordK L wd (Nat.sub e s) s k0))))))

@[expose] noncomputable def rhoC (pp pj : Nat → Nat) (L : Nat → Nat → Nat) (ρ : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) ρ, Nat.beq (tm pp pj L ρ (tm pp pj L ρ ρ)) (nat_lit 0))

@[expose] noncomputable def genC (pp pj gi : Nat → Nat) (n : Nat) : Bool :=
  allN (nat_lit 3) fun j => strictB (gi j) fun i => bAnd(Nat.blt (nat_lit 0) i,
    bAnd(Nat.blt i n, bAnd(Nat.beq (pp i) (nat_lit 0), Nat.beq (pj i) j)))

@[expose] noncomputable def closC (pp pj : Nat → Nat) (L : Nat → Nat → Nat) (gi X : Nat → Nat)
    (q : Nat → Nat → Nat) (ρ c p n : Nat) : Bool :=
  bAnd(Nat.ble c (nat_lit 9), bAnd(Nat.blt p c, bAnd(Nat.beq (X p) ρ,
    allBlk (nat_lit 0) (fun u => strictB (X u) fun x => bAnd(Nat.blt x n,
      allBlk (nat_lit 0) (fun j => strictB (q u j) fun v => strictB (gi j) fun g =>
        bAnd(Nat.blt v c, Nat.beq (tm pp pj L g x) (tm pp pj L (X v) g))) (nat_lit 3))) c)))

@[expose] noncomputable def conjgC (pp pj : Nat → Nat) (L : Nat → Nat → Nat) (ct cx : Nat → Nat)
    (ρ n m : Nat) : Bool :=
  strictB (ct m) fun t => strictB (cx m) fun x => bAnd(Nat.blt t n, bAnd(Nat.blt x n,
    bAnd(bIf(Nat.beq m (nat_lit 0), true, Nat.blt (cx (Nat.sub m (nat_lit 1))) x),
      Nat.beq (tm pp pj L t ρ) (tm pp pj L x t))))

end CFSG.KC.Fi22Cls

end
