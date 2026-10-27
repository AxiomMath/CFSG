module

public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Sporadic.Schreier.TitsArrays
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import Certificates.Data.Thm49ECore
public import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.KD.T49

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def lenK {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def allK {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) l

@[expose] noncomputable def ap (P x : Nat) : Nat := pg (nat_lit 11) (mask (nat_lit 11)) P x

@[expose] noncomputable def pmul (P Q : Nat) : Nat :=
  pcomp (nat_lit 1755) (nat_lit 11) (mask (nat_lit 11)) P Q

@[expose] noncomputable def idP : Nat := pidn (nat_lit 1755) (nat_lit 11)

@[expose] noncomputable def wd (S SI : Nat → Nat) (w : List Int) : Nat :=
  wordK (nat_lit 1755) (nat_lit 11) (mask (nat_lit 11)) idP S SI w

@[expose] noncomputable def isPerm (P Q : Nat) : Bool :=
  permOK (nat_lit 1755) (nat_lit 11) (mask (nat_lit 11)) (nat_lit 19305) P Q

@[expose] noncomputable def commP (P Q : Nat) : Bool := Nat.beq (pmul P Q) (pmul Q P)

@[expose] noncomputable def bitK (S x : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight S x) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def setK (S x : Nat) : Nat := Nat.lor S (Nat.shiftLeft (nat_lit 1) x)

@[expose] noncomputable def recY (r : Nat) : Nat := Nat.land r (nat_lit 2047)

@[expose] noncomputable def recP (r : Nat) : Nat := Nat.land (Nat.shiftRight r (nat_lit 11)) (nat_lit 2047)

@[expose] noncomputable def recG (r : Nat) : Nat := Nat.shiftRight r (nat_lit 22)

@[expose] noncomputable def pick2 (G0 G1 g : Nat) : Nat := nIf(Nat.beq g (nat_lit 0), G0, G1)

@[expose] noncomputable def orbOK (G0 G1 : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih S => bAnd(Nat.blt (recG r) (nat_lit 2), bAnd(bitK S (recP r),
      bAnd(bIf(bitK S (recY r), false, true),
      bAnd(Nat.beq (ap (pick2 G0 G1 (recG r)) (recP r)) (recY r), ih (setK S (recY r)))))))

@[expose] noncomputable def orbMask : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S) (fun r _ ih S => ih (setK S (recY r)))

structure F6W where
  F : Nat → Nat
  FI : Nat → Nat
  D : Nat → Nat
  DI : Nat → Nat
  Z : Nat
  ew : List Int
  e1w : List Int
  e1iw : List Int
  fw : List Int
  fz : List Nat
  fzz : List Nat
  q0 : Nat
  yp : Nat
  r2 : Nat
  o1 : List Nat
  o2 : List Nat

@[expose] noncomputable def f6Core (W : F6W) (zp y0 u1 u2 e e1 e1i f : Nat) : Bool :=
  bAnd(commP zp W.Z, bAnd(Nat.blt W.q0 (nat_lit 1755),
  bAnd(bIf(Nat.beq (ap zp W.q0) (ap W.Z W.q0), false, true),
  bAnd(Nat.beq (pmul e W.Z) (pmul zp e), bAnd(Nat.beq (ap e (nat_lit 0)) W.yp,
  bAnd(Nat.beq (pmul y0 W.Z) (pmul zp y0), bAnd(Nat.beq (pmul y0 zp) (pmul W.Z y0),
  bAnd(fixedK (nat_lit 1755) (nat_lit 11) (mask (nat_lit 11)) W.Z W.fz,
  bAnd(fixedK (nat_lit 1755) (nat_lit 11) (mask (nat_lit 11)) (pmul W.Z zp) W.fzz,
  bAnd(bIf(Nat.beq (lenK W.fz) (lenK W.fzz), false, true),
  bAnd(Nat.beq (ap u1 (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (ap u2 (nat_lit 0)) (nat_lit 0),
  bAnd(commP u1 W.Z, bAnd(commP u2 W.Z,
  bAnd(Nat.beq (ap e1 (nat_lit 0)) W.r2, bAnd(Nat.beq (pmul e1 e1i) idP,
  bAnd(Nat.beq (pmul (pmul (pmul W.Z (pmul e1 W.Z)) e1i) f) (pmul f W.Z),
  bAnd(orbOK u1 u2 W.o1 (setK (nat_lit 0) W.yp), bAnd(orbOK u1 u2 W.o2 (setK (nat_lit 0) W.r2),
  bAnd(Nat.beq (lenK W.o1) (nat_lit 79),
  strictB (orbMask W.o1 (setK (nat_lit 0) W.yp)) (fun M1 =>
  strictB (orbMask W.o2 (setK (nat_lit 0) W.r2)) (fun M2 =>
  allK (fun y => bIf(Nat.beq y (nat_lit 0), true, bIf(bitK M1 y, true, bitK M2 y))) W.fz))))))))))))))))))))))

@[expose] noncomputable def f6K (W : F6W) : Bool :=
  bAnd(allN (nat_lit 4) (fun j => isPerm (W.F j) (W.FI j)),
  bAnd(allN (nat_lit 2) (fun j => isPerm (W.D j) (W.DI j)), bAnd(isPerm W.Z W.Z,
  bAnd(lettersK (nat_lit 4) Certificates.Thm49E.zpWord,
  bAnd(lettersK (nat_lit 4) Certificates.Thm49E.y0Word,
  bAnd(lettersK (nat_lit 4) Certificates.Thm49E.u1Word,
  bAnd(lettersK (nat_lit 4) Certificates.Thm49E.u2Word,
  bAnd(lettersK (nat_lit 2) W.ew, bAnd(lettersK (nat_lit 2) W.e1w,
  bAnd(lettersK (nat_lit 2) W.e1iw, bAnd(lettersK (nat_lit 2) W.fw,
  strictB (wd W.F W.FI Certificates.Thm49E.zpWord) (fun zp =>
  strictB (wd W.F W.FI Certificates.Thm49E.y0Word) (fun y0 =>
  strictB (wd W.F W.FI Certificates.Thm49E.u1Word) (fun u1 =>
  strictB (wd W.F W.FI Certificates.Thm49E.u2Word) (fun u2 =>
  strictB (wd W.D W.DI W.ew) (fun e =>
  strictB (wd W.D W.DI W.e1w) (fun e1 =>
  strictB (wd W.D W.DI W.e1iw) (fun e1i =>
  strictB (wd W.D W.DI W.fw) (fun f =>
    f6Core W zp y0 u1 u2 e e1 e1i f)))))))))))))))))))

structure F6OK (W : F6W) : Prop where
  bindF : ∀ j < 4, CFSG.Sporadic.Schreier.Tits.titsGenArrs[j]! = unpack 1755 11 (W.F j)
  bindD : ∀ j < 2, CFSG.Sporadic.Schreier.Tits.titsDerivedArrs[j]! = unpack 1755 11 (W.D j)
  bindZ : CFSG.Sporadic.Schreier.Tits.titsZArr = unpack 1755 11 W.Z
  check : f6K W = true

end CFSG.KD.T49

end
