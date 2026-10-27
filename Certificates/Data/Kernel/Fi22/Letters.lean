module

public import Certificates.Data.Kernel.Fi22.Orb
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.Fi22L

open CFSG.KC.Enum CFSG.Sporadic.Fi22.Native

@[expose] def ljText : String := include_str "lj.hex"

@[expose] noncomputable def ljPacked : Nat := by hex_nat ljText 1579500 12450172884146417421

@[expose] def slpText : String := include_str "ljslp.hex"

@[expose] noncomputable def slpPacked : Nat := by hex_nat slpText 564 13229530168285928549

@[expose] noncomputable def wM (m : Nat) : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) m) (nat_lit 1)

@[expose] noncomputable def tM : Nat := wM (nat_lit 42120)

@[expose] noncomputable def tabK (P t : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul (nat_lit 42120) t)) tM

@[expose] noncomputable def orbT (t : Nat) : Nat :=
  Nat.land (Nat.shiftRight orbPacked (Nat.mul (nat_lit 42120) t)) tM

@[expose] noncomputable def regT (P k : Nat) : Nat :=
  nIf(Nat.blt k (nat_lit 2), orbT k, nIf(Nat.beq k (nat_lit 2), tabK P (nat_lit 0),
    nIf(Nat.beq k (nat_lit 3), orbT (nat_lit 0), tabK P (Nat.sub k (nat_lit 3)))))

@[expose] noncomputable def lk (T y : Nat) : Nat := fld(T, Nat.mul (nat_lit 12) y, nat_lit 4095)

@[expose] noncomputable def reg (P k y : Nat) : Nat := lk (regT P k) y

@[expose] noncomputable def invL (P j y : Nat) : Nat := lk (tabK P (Nat.add (nat_lit 134) j)) y

@[expose] noncomputable def wrOf (S j : Nat) : Nat := fld(S, Nat.mul (nat_lit 8) j, nat_lit 255)

@[expose] noncomputable def raOf (S k : Nat) : Nat :=
  fld(S, Nat.mul (nat_lit 8) (Nat.add (nat_lit 16) (Nat.mul (nat_lit 2) (Nat.sub k (nat_lit 4)))),
    nat_lit 255)

@[expose] noncomputable def rbOf (S k : Nat) : Nat :=
  fld(S, Nat.mul (nat_lit 8) (Nat.succ (Nat.add (nat_lit 16)
    (Nat.mul (nat_lit 2) (Nat.sub k (nat_lit 4))))), nat_lit 255)

@[expose] noncomputable def chOf (c : Nat) : Char :=
  Bool.rec (motive := fun _ => Char) (Bool.rec (motive := fun _ => Char) 'A' 'B' (Nat.beq c (nat_lit 2)))
    (Bool.rec (motive := fun _ => Char) 'b' 'a' (Nat.beq c (nat_lit 0))) (Nat.blt c (nat_lit 2))

@[expose] noncomputable def exF (S f : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun k => [k])
    (fun _ ih k => Bool.rec (motive := fun _ => List Nat) (List.append (ih (raOf S k)) (ih (rbOf S k)))
      [k] (Nat.blt k (nat_lit 4))) f

@[expose] noncomputable def genChkK (P : Nat) : Bool :=
  allN (nat_lit 3510) fun y => bAnd(Nat.blt (reg P (nat_lit 0) y) (nat_lit 3510),
    bAnd(Nat.blt (reg P (nat_lit 1) y) (nat_lit 3510), bAnd(Nat.blt (reg P (nat_lit 2) y) (nat_lit 3510),
    bAnd(Nat.beq (reg P (nat_lit 2) (reg P (nat_lit 1) y)) y,
      Nat.beq (reg P (nat_lit 1) (reg P (nat_lit 2) y)) y))))

@[expose] noncomputable def ruleChkK (P S k : Nat) : Bool :=
  strictB (raOf S k) fun a => strictB (rbOf S k) fun b =>
    bAnd(Nat.blt a k, bAnd(Nat.blt b k,
      allN (nat_lit 3510) fun x => Nat.beq (reg P k x) (reg P a (reg P b x))))

@[expose] noncomputable def invChkK (P S j : Nat) : Bool :=
  strictB (wrOf S j) fun r => allN (nat_lit 3510) fun x =>
    bAnd(Nat.blt (invL P j x) (nat_lit 3510),
      bAnd(Nat.beq (invL P j (reg P r x)) x, Nat.beq (reg P r (invL P j x)) x))

@[expose] noncomputable def wrChkK (S : Nat) : Bool :=
  allN (nat_lit 16) fun j => Nat.blt (wrOf S j) (nat_lit 137)

@[expose] noncomputable def LJk (P S l x : Nat) : Nat :=
  nIf(Nat.beq (Nat.land l (nat_lit 1)) (nat_lit 0), reg P (wrOf S (Nat.shiftRight l (nat_lit 1))) x,
    invL P (Nat.shiftRight l (nat_lit 1)) x)

end CFSG.KS.Fi22L

end
