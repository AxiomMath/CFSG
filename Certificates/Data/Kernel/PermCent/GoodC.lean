module

public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheck

public section

namespace CFSG.Certificates.Kernel.PkCV.Good

open CFSG.ClassicalInvolution.Q3.TA3.Check

variable {n : Nat} [Small n]

@[expose] noncomputable def ordAuxC (o : CV n) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, k => bif powOneC o k then k else ordAuxC o fuel (k + 1)

@[expose] noncomputable def ordC (B : Nat) (o : CV n) : Nat := ordAuxC o B 1

@[expose] noncomputable def centC (L : List (CV n)) (t : CV n) : List (CV n) :=
  L.filter fun c => eq22C c t t c

@[expose] noncomputable def noOddC (B : Nat) (C : List (CV n)) : Bool :=
  C.all fun o => decide (ordC B o ≠ 0) &&
    (decide (o = 1) || decide (ordC B o % 2 = 0) ||
      C.any fun c => decide (ordC B (o * (c * o * c⁻¹)) ≠ 0) &&
        decide (ordC B (o * (c * o * c⁻¹)) % 2 = 0))

@[expose] noncomputable def goodC (B : Nat) (L : List (CV n)) : Bool :=
  L.all fun t => !(powOneC t 2 && !decide (t = 1)) ||
    (let C := centC L t; noOddC B C && pairsB t C)

end CFSG.Certificates.Kernel.PkCV.Good

end
