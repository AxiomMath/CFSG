module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Loop CFSG.KC.Enum

@[expose] noncomputable def actMK (cs : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun c _ ih m => Nat.xor (nIf(Nat.beq (Nat.land m (nat_lit 1)) (nat_lit 1), c, nat_lit 0))
      (ih (Nat.shiftRight m (nat_lit 1)))) cs m

@[expose] noncomputable def fixLstQ (M F : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun f _ ih => Bool.rec (motive := fun _ => List Nat) ih (f :: ih) (Nat.beq (actMK M f) f)) F

@[expose] noncomputable def lenK {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def lAllK {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) l

@[expose] noncomputable def nAllK (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(f j, ih)) n

@[expose] noncomputable def quadK (n : Nat) (Ms : List (List Nat)) : Bool :=
  lAllK Ms fun s => lAllK Ms fun t => nAllK n fun j =>
    strictB (Nat.xor (actMK t (Nat.shiftLeft (nat_lit 1) j)) (Nat.shiftLeft (nat_lit 1) j))
      fun v => Nat.beq (actMK s v) v

@[expose] noncomputable def cmpQK (n : Nat) (strict : Bool) (k c : Nat) : Bool :=
  bIf(strict,
    bAnd(Nat.blt (Nat.mul (nat_lit 2) k) n, bIf(Nat.beq c (nat_lit 0), true,
      Nat.blt c (Nat.shiftLeft (nat_lit 1) (Nat.sub n (Nat.mul (nat_lit 2) k))))),
    bAnd(Nat.ble (Nat.mul (nat_lit 2) k) n, bIf(Nat.beq c (nat_lit 0), true,
      Nat.blt c (Nat.shiftLeft (nat_lit 1) (Nat.succ (Nat.sub n (Nat.mul (nat_lit 2) k)))))))

@[expose] noncomputable def predQK (n : Nat) (strict : Bool) (Ms : List (List Nat)) (F : List Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun _ _ _ => bIf(quadK n Ms, cmpQK n strict (lenK Ms) (lenK F), true)) Ms

end CFSG.KC.HMathieu

end
