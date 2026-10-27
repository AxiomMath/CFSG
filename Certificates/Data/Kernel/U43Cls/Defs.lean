module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.U43Cls

open CFSG.KC.Enum

@[expose] noncomputable def wP (G : Nat → Nat → Nat) (W len q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun j ih q => strictN (G fld(W, Nat.mul (nat_lit 5) j, nat_lit 31) q) ih) len q

@[expose] noncomputable def wPI (Gi : Nat → Nat → Nat) (W len q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun j ih q => strictN (ih q) (fun v => Gi fld(W, Nat.mul (nat_lit 5) j, nat_lit 31) v)) len q

@[expose] noncomputable def cjP (G Gi : Nat → Nat → Nat) (a : Nat → Nat) (W len q : Nat) : Nat :=
  strictN (wPI Gi W len q) (fun u => strictN (a u) (fun v => wP G W len v))

@[expose] noncomputable def lettersOK (k W len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih => bAnd(Nat.blt fld(W, Nat.mul (nat_lit 5) j, nat_lit 31) k, ih)) len

@[expose] noncomputable def ncommAt (f y yi : Nat → Nat) (p : Nat) : Bool :=
  strictB (f p) (fun fp =>
  strictB (strictN (yi p) (fun u => strictN (f u) y)) (fun gp =>
    bIf(Nat.beq (f gp) (strictN (yi fp) (fun u => strictN (f u) y)), false, true)))

@[expose] noncomputable def cRec (R : Nat → Nat) (G Gi : Nat → Nat → Nat) (a : Nat → Nat)
    (Y Yi : Nat → Nat → Nat) (k p₀ p₁ p₂ i : Nat) : Bool :=
  strictB (R i) (fun r =>
  strictB fld(r, nat_lit 0, nat_lit 33554431) (fun W =>
  strictB fld(r, nat_lit 25, nat_lit 7) (fun len =>
  strictB fld(r, nat_lit 58, nat_lit 1) (fun kind =>
  strictB fld(r, nat_lit 59, nat_lit 3) (fun wp =>
  bAnd(lettersOK k W len,
  bAnd(Nat.beq (cjP G Gi a W len p₀) fld(r, nat_lit 28, nat_lit 1023),
  bAnd(Nat.beq (cjP G Gi a W len p₁) fld(r, nat_lit 38, nat_lit 1023),
  bAnd(Nat.beq (cjP G Gi a W len p₂) fld(r, nat_lit 48, nat_lit 1023),
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
      Nat.blt fld(R (Nat.sub i (nat_lit 1)), nat_lit 28, nat_lit 1073741823)
        fld(r, nat_lit 28, nat_lit 1073741823)),
  bAnd(Nat.blt wp (nat_lit 3),
    ncommAt (cjP G Gi a W len) (Y kind) (Yi kind)
      (nIf(Nat.beq wp (nat_lit 0), p₀, nIf(Nat.beq wp (nat_lit 1), p₁, p₂))))))))))))))

@[expose] noncomputable def cBlk (R : Nat → Nat) (G Gi : Nat → Nat → Nat) (a : Nat → Nat)
    (Y Yi : Nat → Nat → Nat) (k p₀ p₁ p₂ n c : Nat) : Bool :=
  strictB (Nat.mul (nat_lit 64) c) (fun b =>
    allBlk b (cRec R G Gi a Y Yi k p₀ p₁ p₂)
      (nIf(Nat.blt (Nat.sub n b) (nat_lit 64), Nat.sub n b, nat_lit 64)))

end CFSG.KC.U43Cls

end
