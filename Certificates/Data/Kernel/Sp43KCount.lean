module

public import Certificates.Data.Sp43.Code

public section

namespace CFSG.KC.Sp43K

open CFSG.Sp43.Native

@[expose] def cntRow (f : Nat → Nat → Bool) (x : Nat) : Nat :=
  Nat.rec 0 (fun y acc => acc + if f x y then 1 else 0) 81

@[expose] def cnt2 (f : Nat → Nat → Bool) : Nat :=
  Nat.rec 0 (fun x acc => acc + cntRow f x) 81

@[expose] def xCond (x y : Nat) : Bool := omg x y == 2

@[expose] def hCond (r₁ r₃ : Nat) : Bool :=
  omg 9 r₃ == 0 && omg r₁ 9 == 0 && omg r₁ r₃ == 2 && omg 1 r₁ == 0 && omg 1 9 == 2 &&
    omg 1 r₃ == 0

@[expose] def cntK (f : Nat → Nat → Bool) (n : Nat) : Bool := cnt2 f == n

@[expose] def cxC : Bool := cntK xCond 2160

@[expose] def chC : Bool := cntK hCond 24

end CFSG.KC.Sp43K

end
