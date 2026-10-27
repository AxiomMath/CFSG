module

public import Certificates.Data.Kernel.PermCent.CV

public section

namespace CFSG.Certificates.Kernel.PkCV.L33R

variable {n : Nat} [Small n]

@[expose] noncomputable def oddCoreAtC (m : Nat) (CA CP : List (CV n)) : Bool :=
  CA.all fun x =>
    bif !decide (x = 1) && powOneC x m then CP.any fun c => !powOneC (x * c * x⁻¹ * c⁻¹) m
    else true

@[expose] noncomputable def oddCoreRepC (m : Nat) (LA LP : List (CV n)) (τ : CV n) : Bool :=
  oddCoreAtC m (LA.filter fun g => eq22C g τ τ g) (LP.filter fun c => eq22C c τ τ c)

@[expose] noncomputable def ordRunC (o : CV n) : Nat → CV n → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, acc, k => if acc = 1 then k else ordRunC o fuel (acc * o) (k + 1)

@[expose] noncomputable def ordBC (B : Nat) (o : CV n) : Nat := ordRunC o B o 1

@[expose] noncomputable def noOddBC (B : Nat) (C : List (CV n)) : Bool :=
  C.all fun o => decide (ordBC B o ≠ 0) &&
    (decide (o = 1) || decide (ordBC B o % 2 = 0) ||
      C.any fun c => decide (ordBC B (o * (c * o * c⁻¹)) ≠ 0) &&
        decide (ordBC B (o * (c * o * c⁻¹)) % 2 = 0))

@[expose] noncomputable def memC (L : List (CV n)) (x : CV n) : Bool := L.any fun s => decide (s = x)

@[expose] noncomputable def q8C (t a b : CV n) : List (CV n) :=
  [1, a, t, t * a, b, b * a, b * t, b * (t * a)]

@[expose] noncomputable def pairsNC (LN : List (CV n)) (t : CV n) (C : List (CV n)) : Bool :=
  (C.filter fun a => decide (a * a = t)).all fun a =>
    (C.filter fun b => decide (b * b = t)).all fun b =>
      !decide (b * a = t * a * b) ||
      !(C.all fun c => memC (q8C t a b) (c * a * c⁻¹) && memC (q8C t a b) (c * b * c⁻¹)) ||
      (memC LN a && memC LN b) ||
      C.any fun x => powOneC x 3 && !(eq22C x a a x && eq22C x b b x) &&
        C.all fun y => !(eq22C y a a y && eq22C y b b y) || eq22C x y y x

@[expose] noncomputable def goodAtC (B : Nat) (LN L : List (CV n)) (t : CV n) : Bool :=
  let C := L.filter fun c => eq22C c t t c
  noOddBC B C && pairsNC LN t C

end CFSG.Certificates.Kernel.PkCV.L33R

end
