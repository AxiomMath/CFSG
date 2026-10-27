module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.Fi22U

open CFSG.KC.Enum CFSG.KS

@[expose] def wOf (l : List Nat) : List Int :=
  l.map fun x => if x % 2 = 0 then ((x / 2 + 1 : Nat) : Int) else -((x / 2 + 1 : Nat) : Int)

@[expose] def flipC (x : Nat) : Nat := if x % 2 = 0 then x + 1 else x - 1

@[expose] def ninvC (u : List Nat) : List Nat := (u.map flipC).reverse

@[expose] def commC (a₀ b₀ a₁ b₁ : List Nat) : List Nat :=
  b₀ ++ a₀ ++ ninvC b₀ ++ ninvC a₀ ++ b₁ ++ a₁ ++ ninvC b₁ ++ ninvC a₁

@[expose] noncomputable def invOK (CU INV : Nat) : Bool :=
  allN 693 fun j => Nat.beq (pg 10 (mask 10) INV (pg 10 (mask 10) CU j)) j

@[expose] noncomputable def restrictOK (CU INV S G MP : Nat) : Bool :=
  allN 693 fun j => Nat.beq
    (pg 12 (mask 12) MP (pg 10 (mask 10) INV (pg 10 (mask 10) S (pg 10 (mask 10) CU j))))
    (pg 12 (mask 12) G (pg 12 (mask 12) MP j))

@[expose] noncomputable def fixOK (Z MP : Nat) : Bool :=
  allN 693 fun j => Nat.beq (pg 12 (mask 12) Z (pg 12 (mask 12) MP j)) (pg 12 (mask 12) MP j)

@[expose] noncomputable def distinctOK (MP : Nat) : Bool :=
  allN 693 fun i => allN i fun j =>
    Bool.rec (motive := fun _ => Bool) true false (Nat.beq (pg 12 (mask 12) MP i) (pg 12 (mask 12) MP j))

end CFSG.KC.Fi22U

end
