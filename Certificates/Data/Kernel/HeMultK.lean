module

public import Certificates.Data.Kernel.HeTabK

public section

namespace CFSG.KC.HeMult

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KC.HeTab

@[expose] noncomputable def GAC (AL CT : Nat → Nat) (z : Int) (x : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => nIf(Nat.beq k (nat_lit 1), r32 AL x, r32 CT x))
    (fun _ => r32 CT x) z

@[expose] noncomputable def GL (U V S T Ui Vi Si Ti : Nat → Nat) (z : Int) (x : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => nIf(Nat.beq k (nat_lit 1), r32 U x, nIf(Nat.beq k (nat_lit 2), r32 V x,
      nIf(Nat.beq k (nat_lit 3), r32 S x, nIf(Nat.beq k (nat_lit 4), r32 T x, r32 Ti x)))))
    (fun k => nIf(Nat.beq k (nat_lit 0), r32 Ui x, nIf(Nat.beq k (nat_lit 1), r32 Vi x,
      nIf(Nat.beq k (nat_lit 2), r32 Si x, r32 Ti x)))) z

@[expose] noncomputable def itK (W : Nat → Nat) (e x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ y => r32 W y) e

@[expose] noncomputable def cK (AL BE BI CT : Nat → Nat) (cw : List Int) (x : Nat) : Bool :=
  Nat.beq (r32 CT x) (List.foldr (GK AL BE BI) x cw)

@[expose] noncomputable def invK (X Xi : Nat → Nat) (x : Nat) : Bool :=
  bAnd(Nat.blt (r32 Xi x) (nat_lit 8330), Nat.beq (r32 Xi (r32 X x)) x)

@[expose] noncomputable def powK (AL CT W X Xi : Nat → Nat) (w : List Int) (e x : Nat) : Bool :=
  bAnd(Nat.beq (r32 W x) (List.foldr (GAC AL CT) x w),
    bAnd(Nat.beq (r32 X x) (itK W e x), invK X Xi x))

@[expose] noncomputable def tK (AL BE BI X Xi : Nat → Nat) (w : List Int) (x : Nat) : Bool :=
  bAnd(Nat.beq (r32 X x) (List.foldr (GK AL BE BI) x w), invK X Xi x)

@[expose] noncomputable def relK (AL BE U V S T Ui Vi Si Ti : Nat → Nat) (ws : List (List Int))
    (sa sb : List Int) (x : Nat) : Bool :=
  bAnd(List.all ws fun w => Nat.beq (List.foldr (GL U V S T Ui Vi Si Ti) x w) x,
  bAnd(Nat.beq (List.foldr (GL U V S T Ui Vi Si Ti) x sa) (r32 AL x),
    Nat.beq (List.foldr (GL U V S T Ui Vi Si Ti) x sb) (r32 BE x)))

end CFSG.KC.HeMult

end
