module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.AxisCount.BabyIdent
public import CFSG.Monster.B.TwoA.Triality.PermLift

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount.Baby

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.Short

open CFSG.Monster.B.TwoA (hE0)

@[expose] def shapeOK : Bool := (List.range 10).all fun j =>
  (bo j).kappaPlus.size == (bo j).h.size && (bo j).kappaMinus.size == (bo j).h.size &&
    (bo j).tPlus.size == (bo j).h.size && (bo j).tMinus.size == (bo j).h.size &&
    (bo j).size.size == (bo j).h.size && (bo j).lam.size == (bo j).h.size

@[expose] def tfin (j r : ℕ) (ε : Bool) : Fin 10 := ⟨tgt j r ε % 10, Nat.mod_lt _ (by norm_num)⟩

end CFSG.Monster.AxisCount.Baby
