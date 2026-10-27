
module

public import CFSG.Monster.B.TwoA.Sp8.LiftsBase
public import CFSG.Monster.Visible.SignCompat.Triality
public meta import CFSG.Monster.B.Rep4371.Model

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts CFSG.Monster.VisQuot CFSG.Monster.B.Co2

@[expose] def ySqRowCheck (eY : ℕ → Bool → ℕ → Bool × Bool × ℕ) : Bool :=
  (List.range 4096).all fun c => [false, true].all fun η =>
    let r := eY 3 η c
    let r' := eY 3 r.2.1 r.2.2
    (r.1 ^^ r'.1, r'.2.1, r'.2.2) == (false, η, Model.pi0N c)

end CFSG.Monster.B.TwoA.Sp8
