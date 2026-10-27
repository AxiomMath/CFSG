module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KC.HeTab

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

@[expose] noncomputable def GK (AL BE BI : Nat → Nat) (z : Int) (x : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => nIf(Nat.beq k (nat_lit 1), r32 AL x, nIf(Nat.beq k (nat_lit 2), r32 BE x, r32 BI x)))
    (fun k => nIf(Nat.beq k (nat_lit 0), r32 AL x, r32 BI x)) z

@[expose] noncomputable def invBK (BE BI : Nat → Nat) (x : Nat) : Bool :=
  bAnd(Nat.blt (r32 BI x) (nat_lit 8330), Nat.beq (r32 BI (r32 BE x)) x)

@[expose] noncomputable def wordK (AL BE BI W : Nat → Nat) (w : List Int) (x : Nat) : Bool :=
  Nat.beq (r32 W x) (List.foldr (GK AL BE BI) x w)

@[expose] noncomputable def e8K (X Y Z : Nat → Nat) (x : Nat) : Bool :=
  bAnd(Nat.beq (r32 X (r32 X x)) x, bAnd(Nat.beq (r32 Y (r32 Y x)) x,
  bAnd(Nat.beq (r32 Z (r32 Z x)) x, bAnd(Nat.beq (r32 X (r32 Y x)) (r32 Y (r32 X x)),
  bAnd(Nat.beq (r32 X (r32 Z x)) (r32 Z (r32 X x)), Nat.beq (r32 Y (r32 Z x)) (r32 Z (r32 Y x)))))))

@[expose] noncomputable def movesK (f g : Nat → Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true false (allN (nat_lit 8330) fun x => Nat.beq (f x) (g x))

end CFSG.KC.HeTab

end
