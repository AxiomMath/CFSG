module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.U43Swap

open CFSG.KC.Enum

@[expose] noncomputable def lp (P : Nat → Nat) (e q : Nat) : Nat :=
  pg (nat_lit 10) (nat_lit 1023) (P e) q

@[expose] noncomputable def wp (P : Nat → Nat) (W n q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun k ih q => strictN (lp P fld(W, Nat.mul (nat_lit 3) k, nat_lit 7) q) ih) n q

@[expose] noncomputable def wpI (P : Nat → Nat) (W n q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun k ih q => strictN (ih q)
      (lp P (Nat.xor fld(W, Nat.mul (nat_lit 3) k, nat_lit 7) (nat_lit 4)))) n q

@[expose] noncomputable def sp (P : Nat → Nat) (e q : Nat) : Nat :=
  strictN (lp P (nat_lit 2) q) (fun q₁ =>
  strictN (fpow (lp P (nat_lit 1)) (Nat.div e (nat_lit 3)) q₁) (fun q₂ =>
  strictN (lp P (nat_lit 6) q₂) (fun q₃ =>
    fpow (lp P (nat_lit 1)) (Nat.mod e (nat_lit 3)) q₃)))

@[expose] noncomputable def spI (P : Nat → Nat) (e q : Nat) : Nat :=
  strictN (fpow (lp P (nat_lit 5)) (Nat.mod e (nat_lit 3)) q) (fun q₁ =>
  strictN (lp P (nat_lit 2) q₁) (fun q₂ =>
  strictN (fpow (lp P (nat_lit 5)) (Nat.div e (nat_lit 3)) q₂) (fun q₃ =>
    lp P (nat_lit 6) q₃)))

@[expose] noncomputable def rl (r : Nat) : Nat := fld(r, nat_lit 24, nat_lit 15)

@[expose] noncomputable def cp (P : Nat → Nat) (r e q : Nat) : Nat :=
  strictN (wpI P r (rl r) q) (fun q₁ => strictN (sp P e q₁) (fun q₂ => wp P r (rl r) q₂))

@[expose] noncomputable def cpI (P : Nat → Nat) (r e q : Nat) : Nat :=
  strictN (wpI P r (rl r) q) (fun q₁ => strictN (spI P e q₁) (fun q₂ => wp P r (rl r) q₂))

@[expose] noncomputable def oE (r : Nat) : Nat := fld(r, nat_lit 28, nat_lit 15)

@[expose] noncomputable def oK (r : Nat) : Nat := fld(r, nat_lit 32, nat_lit 1073741823)

@[expose] noncomputable def oEl (P : Nat → Nat) (r q : Nat) : Nat := cp P r (oE r) q

@[expose] noncomputable def oElI (P : Nat → Nat) (r q : Nat) : Nat := cpI P r (oE r) q

@[expose] noncomputable def oConj (P : Nat → Nat) (r : Nat) (f : Nat → Nat) (q : Nat) : Nat :=
  strictN (oElI P r q) (fun q₁ => strictN (f q₁) (fun q₂ => oEl P r q₂))

@[expose] noncomputable def keyOK (k : Nat) (f : Nat → Nat) : Bool :=
  bAnd(Nat.beq fld(k, nat_lit 0, nat_lit 1023) (f (nat_lit 0)),
    bAnd(Nat.beq fld(k, nat_lit 10, nat_lit 1023) (f (nat_lit 1)),
      Nat.beq fld(k, nat_lit 20, nat_lit 1023) (f (nat_lit 9))))

@[expose] noncomputable def eqB (f g : Nat → Nat) : Bool :=
  bAnd(Nat.beq (f (nat_lit 0)) (g (nat_lit 0)),
    bAnd(Nat.beq (f (nat_lit 1)) (g (nat_lit 1)), Nat.beq (f (nat_lit 9)) (g (nat_lit 9))))

@[expose] noncomputable def bpt (p : Nat) : Nat :=
  nIf(Nat.beq p (nat_lit 0), nat_lit 0, nIf(Nat.beq p (nat_lit 1), nat_lit 1, nat_lit 9))

@[expose] noncomputable def ncw (f g : Nat → Nat) (p : Nat) : Bool :=
  strictB (bpt p) (fun b => bIf(Nat.beq (f (g b)) (g (f b)), false, true))

@[expose] noncomputable def cmB (f g : Nat → Nat) : Bool :=
  eqB (fun q => f (g q)) (fun q => g (f q))

@[expose] noncomputable def yE (k : Nat) : Nat := nIf(Nat.blt k (nat_lit 4), nat_lit 1, nat_lit 3)

@[expose] noncomputable def yEl (P Y : Nat → Nat) (k q : Nat) : Nat := cp P (Y k) (yE k) q

@[expose] noncomputable def oKey (P O : Nat → Nat) (i : Nat) : Bool :=
  strictB (O i) (fun r =>
    bAnd(bIf(Nat.beq i (nat_lit 0), true, Nat.blt (oK (O (Nat.sub i (nat_lit 1)))) (oK r)),
      bAnd(Nat.blt (oE r) (nat_lit 9), keyOK (oK r) (oEl P r))))

@[expose] noncomputable def oCl (P O : Nat → Nat) (i : Nat) : Bool :=
  strictB (O i) (fun r => allN (nat_lit 4) (fun j =>
    strictB fld(r, Nat.add (nat_lit 62) (Nat.mul (nat_lit 7) j), nat_lit 127) (fun c =>
      bAnd(Nat.blt c (nat_lit 81),
        keyOK (oK (O c)) (fun q => lp P j (oEl P r (lp P (Nat.add j (nat_lit 4)) q)))))))

@[expose] noncomputable def oYm (P O Y : Nat → Nat) (i : Nat) : Bool :=
  strictB (O i) (fun r =>
    bAnd(keyOK (Nat.shiftRight (Y fld(r, nat_lit 90, nat_lit 3)) (nat_lit 28))
        (oConj P r (sp P (nat_lit 1))),
      keyOK (Nat.shiftRight (Y (Nat.add (nat_lit 4) fld(r, nat_lit 92, nat_lit 3))) (nat_lit 28))
        (oConj P r (sp P (nat_lit 3)))))

@[expose] noncomputable def t2d (P Y : Nat → Nat) (r t h c : Nat) : Bool :=
  bIf(Nat.beq (Nat.land t (nat_lit 1)) (nat_lit 1),
    ncw (oEl P r) (yEl P Y (Nat.add h fld(t, nat_lit 1, nat_lit 3))) fld(t, nat_lit 3, nat_lit 3),
    allN (nat_lit 4) (fun k =>
      cmB (fun q => lp P (nat_lit 2) (oEl P r (lp P (nat_lit 2) q))) (yEl P Y (Nat.add c k))))

@[expose] noncomputable def oT2 (P O Y : Nat → Nat) (i : Nat) : Bool :=
  strictB (O i) (fun r =>
    bAnd(t2d P Y r fld(r, nat_lit 94, nat_lit 31) (nat_lit 4) (nat_lit 0),
      t2d P Y r fld(r, nat_lit 99, nat_lit 31) (nat_lit 0) (nat_lit 4)))

@[expose] noncomputable def zOK (P O Z : Nat → Nat) : Bool :=
  allN (nat_lit 9) (fun e => strictB (Z e) (fun z =>
    bAnd(Nat.blt z (nat_lit 81), keyOK (oK (O z)) (sp P e))))

@[expose] noncomputable def yRec (P O Y : Nat → Nat) (k : Nat) : Bool :=
  strictB (Y k) (fun r =>
    bAnd(keyOK (Nat.shiftRight r (nat_lit 28)) (cp P r (yE k)),
      strictB fld(r, nat_lit 58, nat_lit 127) (fun o =>
        bAnd(Nat.blt o (nat_lit 81),
          keyOK (Nat.shiftRight r (nat_lit 28)) (oConj P (O o) (sp P (yE k)))))))

@[expose] noncomputable def qRec (P Q : Nat → Nat) (i : Nat) : Bool :=
  strictB (Q i) (fun r =>
    bAnd(bIf(Nat.beq i (nat_lit 0), true,
        Nat.blt (Nat.shiftRight (Q (Nat.sub i (nat_lit 1))) (nat_lit 28)) (Nat.shiftRight r (nat_lit 28))),
      bAnd(keyOK (Nat.shiftRight r (nat_lit 28)) (cp P r (nat_lit 1)),
        keyOK (Nat.shiftRight r (nat_lit 58)) (cp P r (nat_lit 3)))))

@[expose] noncomputable def tRec (P Y T : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) (fun t =>
    ncw (sp P (Nat.succ i)) (yEl P Y fld(t, nat_lit 0, nat_lit 7)) fld(t, nat_lit 3, nat_lit 3))

@[expose] noncomputable def inS1 (e : Nat) : Bool := bIf(Nat.beq e (nat_lit 1), true, Nat.beq e (nat_lit 2))

@[expose] noncomputable def inS2 (e : Nat) : Bool := bIf(Nat.beq e (nat_lit 3), true, Nat.beq e (nat_lit 6))

@[expose] noncomputable def mutS (e₁ e₂ : Nat) : Bool :=
  bIf(inS1 e₁, inS2 e₂, bAnd(inS2 e₁, inS1 e₂))

@[expose] noncomputable def nRec (P O N : Nat → Nat) (n : Nat) : Bool :=
  strictB (Nat.succ (Nat.div n (nat_lit 8))) (fun e₁ =>
  strictB (Nat.succ (Nat.mod n (nat_lit 8))) (fun e₂ =>
    bIf(mutS e₁ e₂, true, strictB (N n) (fun t =>
      strictB fld(t, nat_lit 0, nat_lit 127) (fun o =>
        bAnd(Nat.blt o (nat_lit 81),
          bIf(Nat.beq fld(t, nat_lit 7, nat_lit 1) (nat_lit 0),
            ncw (sp P e₁) (oConj P (O o) (sp P e₂)) fld(t, nat_lit 8, nat_lit 3),
            ncw (sp P e₂) (oConj P (O o) (sp P e₁)) fld(t, nat_lit 8, nat_lit 3))))))))

@[expose] noncomputable def kRec (P K : Nat → Nat) (i : Nat) : Bool :=
  strictB (K i) (fun r =>
    bAnd(bIf(Nat.beq (Nat.mod i (nat_lit 16)) (nat_lit 0), true,
        Nat.blt (Nat.shiftRight (K (Nat.sub i (nat_lit 1))) (nat_lit 28)) (Nat.shiftRight r (nat_lit 28))),
      keyOK (Nat.shiftRight r (nat_lit 28)) (cp P r (Nat.succ (Nat.div i (nat_lit 16))))))

end CFSG.KC.U43Swap

end
