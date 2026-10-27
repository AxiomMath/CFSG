module

public import Certificates.Data.Kernel.Fi23K.Defs

public section

namespace CFSG.KC.Fi23R

open CFSG.KC.Enum CFSG.KC.Fi23K

@[expose] noncomputable def tAf (G : Nat → Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ m => tb G (nat_lit 43) m)
    (fun _ ih k m => nIf(Nat.beq k (nat_lit 0), tb G (nat_lit 43) m,
      strictN (tb G (nat_lit 91) k) fun p =>
        nIf(Nat.beq (tb G (nat_lit 92) k) (nat_lit 1),
          tb G (nat_lit 39) (ih p (tb G (nat_lit 39) m)),
          tb G (nat_lit 40) (ih p (tb G (nat_lit 41) m))))) f

@[expose] noncomputable def tA (G : Nat → Nat) (k m : Nat) : Nat := tAf G (nat_lit 200) k m

@[expose] noncomputable def lf (G : Nat → Nat) (c x : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 128), tb G c x, tA G (Nat.sub c (nat_lit 128)) x)

@[expose] noncomputable def wa (G : Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun c _ ih x => strictN (lf G c x) ih) w x

@[expose] def invL (c : Nat) : Nat := if c = 40 then 41 else if c = 41 then 40 else c

@[expose] def invW (w : List Nat) : List Nat := (w.map invL).reverse

@[expose] def powW (e : Nat) (w : List Nat) : List Nat := (List.replicate e w).flatten

@[expose] def brayW (wR wG : List Nat) (e : Nat) (odd : Bool) : List Nat :=
  cond odd (powW e (wG ++ wR ++ invW wG ++ wR) ++ wG) (powW e (wG ++ wR ++ invW wG ++ wR))

@[expose] def commW (wX wY : List Nat) : List Nat := invW wY ++ invW wX ++ wY ++ wX

@[expose] noncomputable def cntS (q : Nat → Bool) (lo len : Nat) : Nat :=
  foldN len (fun l s => nIf(q (Nat.add lo l), Nat.succ s, s)) (nat_lit 0)

@[expose] noncomputable def fxW (G : Nat → Nat) (w : List Nat) (x : Nat) : Bool :=
  Nat.beq (wa G w x) x

@[expose] noncomputable def eqB (G : Nat → Nat) (u v : List Nat) : Bool :=
  allN (nat_lit 6) fun b => Nat.beq (wa G u b) (wa G v b)

@[expose] noncomputable def wapp (G : Nat → Nat) (gens : List Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih c p => nIf(Nat.beq c (nat_lit 0), p,
      ih (Nat.shiftRight c (nat_lit 4))
        (tA G (List.getD gens (Nat.sub (Nat.land c (nat_lit 15)) (nat_lit 1)) (nat_lit 0)) p))) f

@[expose] noncomputable def orbAt (G : Nat → Nat) (wY : List Nat) (ex : Nat → Bool)
    (W : Nat → Nat) (gens : List Nat) (r₁ r₂ k : Nat) : Bool :=
  bIf(ex k, true, bIf(Nat.beq (wa G wY k) k,
    strictB (W k) fun c => bAnd(Bool.not (Nat.beq c (nat_lit 0)),
      Nat.beq (wapp G gens (nat_lit 7) (Nat.land c (nat_lit 268435455))
        (nIf(Nat.beq (Nat.shiftRight c (nat_lit 28)) (nat_lit 2), r₂, r₁))) k), true))

@[expose] noncomputable def orbSl (G : Nat → Nat) (wY : List Nat) (ex : Nat → Bool)
    (W : Nat → Nat) (gens : List Nat) (r₁ r₂ lo len : Nat) : Bool :=
  allN len fun l => orbAt G wY ex W gens r₁ r₂ (Nat.add lo l)

end CFSG.KC.Fi23R

end
