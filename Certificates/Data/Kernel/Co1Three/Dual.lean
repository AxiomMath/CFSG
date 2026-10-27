module

public import Certificates.Data.Kernel.Co1Three.Slp

public section

namespace CFSG.KC.Co1Cl

open CFSG.KC.Enum CFSG.KC.Co1F2

@[expose] noncomputable def dotK (p : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih x y => Nat.mod (Nat.add (Nat.mul (Nat.mod x p) (Nat.mod y p))
      (ih (Nat.div x p) (Nat.div y p))) p)

@[expose] noncomputable def dualRowK (p n : Nat) (M D : List Nat) : Bool :=
  bAnd(Nat.beq (lenL M) n, bAnd(Nat.beq (lenL D) n,
    allN n fun i => allN n fun j =>
      Nat.beq (dotK p n (getL (nat_lit 0) M i) (getL (nat_lit 0) D j))
        (nIf(Nat.beq i j, nat_lit 1, nat_lit 0))))

@[expose] noncomputable def dualsK (p n : Nat) :
    List (Nat × List Nat) → List (Nat × List Nat) → Bool :=
  fun NZ => List.rec (motive := fun _ => List (Nat × List Nat) → Bool)
    (fun DZ => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) DZ)
    (fun x _ ih DZ => List.rec (motive := fun _ => Bool) false
      (fun y t _ => bAnd(Nat.beq x.1 y.1, bAnd(dualRowK p n x.2 y.2, ih t))) DZ) NZ

end CFSG.KC.Co1Cl

end
