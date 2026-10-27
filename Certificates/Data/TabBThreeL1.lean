module

public import CFSG.Monster.B.Classical.E6AdjointTable
public import CFSG.Fischer.F4
public import Certificates.Certificate114

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

open CFSG.Monster.B.Classical.E6Adjoint CFSG.Fischer

@[expose] def choices (o : ℕ × ℕ) : List F4 :=
  if o.1 = o.2 then [0, 1] else [0, 1, F4.ω, F4.ω * F4.ω]

@[expose] def orbs : List (ℕ × ℕ) :=
  [(7, 7), (15, 15), (27, 26), (39, 34), (38, 38), (50, 45), (49, 49), (58, 54), (55, 55),
    (64, 61), (62, 62), (68, 67), (72, 72), (74, 74), (76, 76)]

end CFSG.HardMathSupport.Dickson.I271.TabBThreeL1
