module

public import CFSG.Certificates.Kernel.Common.HexNat
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.CFSGNative.F4.Unitary

public section

namespace CFSG.KS.T46K

open CFSG.KC.Enum CFSG.F4.Native

@[expose] def t46Text : String := include_str "t46.hex"

@[expose] noncomputable def t46P : Nat := by hex_nat t46Text 222590 12162499037825123670

@[expose] noncomputable def tM : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 8316)) (nat_lit 1)

@[expose] noncomputable def tT (t : Nat) : Nat :=
  Nat.land (Nat.shiftRight t46P (Nat.mul (nat_lit 8316) t)) tM

@[expose] noncomputable def LK (l x : Nat) : Nat := fld(tT l, Nat.mul (nat_lit 12) x, nat_lit 4095)

@[expose] noncomputable def UC (x : Nat) : Nat := LK (nat_lit 106) x

@[expose] noncomputable def GC (j : Nat) : Nat := LK (nat_lit 107) j

@[expose] noncomputable def genAt (j x : Nat) : Bool :=
  strictB (LK (Nat.mul (nat_lit 2) j) x) fun y =>
    bAnd(Nat.blt y (nat_lit 693), Nat.beq (UC y) (normC (tvC (GC j) (UC x))))

@[expose] noncomputable def genSl (j : Nat) : Bool := allN (nat_lit 693) (genAt j)

@[expose] noncomputable def appW (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun g _ ih => LK (Nat.mul (nat_lit 2) g) ih) w

@[expose] noncomputable def wChk (j : Nat) (w : List Nat) : Bool :=
  allN (nat_lit 693) fun x => Nat.beq (LK (Nat.mul (nat_lit 2) j) x) (appW w x)

@[expose] noncomputable def wordK : Bool :=
  bAnd(wChk (nat_lit 46) [nat_lit 0], bAnd(wChk (nat_lit 47) [nat_lit 11],
  bAnd(wChk (nat_lit 48) [nat_lit 21], bAnd(wChk (nat_lit 49) [nat_lit 34],
  bAnd(wChk (nat_lit 50) [nat_lit 18, nat_lit 31, nat_lit 45, nat_lit 31, nat_lit 18],
  bAnd(wChk (nat_lit 51) [nat_lit 11, nat_lit 18, nat_lit 31, nat_lit 45, nat_lit 31, nat_lit 18,
    nat_lit 39, nat_lit 24, nat_lit 18, nat_lit 31, nat_lit 45, nat_lit 31, nat_lit 18, nat_lit 14],
  wChk (nat_lit 52) [nat_lit 11, nat_lit 14, nat_lit 11, nat_lit 18, nat_lit 31, nat_lit 45,
    nat_lit 31, nat_lit 18, nat_lit 39, nat_lit 24, nat_lit 18, nat_lit 31, nat_lit 45, nat_lit 31,
    nat_lit 18, nat_lit 14, nat_lit 14, nat_lit 11]))))))

@[expose] noncomputable def eqLF (F : Nat → Nat) (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih x => bAnd(Nat.beq (F x) c, strictB (Nat.succ x) ih)) l x

end CFSG.KS.T46K

end
