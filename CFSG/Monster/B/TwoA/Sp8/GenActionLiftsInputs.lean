
module

public import CFSG.Monster.B.TwoA.Sp8.ElemAbBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionData
public import CFSG.Monster.B.Gen.HRecords
public meta import CFSG.Monster.B.Rep4371.Model
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionData
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Sp8.LiftsBase
public import CFSG.Monster.B.TwoA.Sp8.ZrelBase
public import CFSG.Monster.Visible.SignCompat.TrialityCycleOctad

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.Lifts CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2

@[expose] def pauliGen (k : ℕ) : Model.Pauli := pauliQs.getD k (false, 0, 0)

@[expose] def signCodesOf (j : ℕ) : List ℕ := (signWords.getD j []).map fun l => 2 ^ (l - 3)

@[expose] def epsDual (j : ℕ) : ℕ := if Model.kappaN fPerms[j]! 63 then 62 else 0

@[expose] def h1ConjN (k : ℕ) (y : Model.Pauli) : Model.Pauli :=
  if k < 23 then Model.conjPauliN (pauliGen k) y
  else if k < 32 then
    Model.conjPauliN (false, 0, epsDual (k - 23)) (Model.conjPermN fPerms[k - 23]! y)
  else if k < 43 then (signCodesOf (k - 32)).foldl (fun x a => Model.conjYN a x) y
  else Model.conjYN 1 (Model.conjXiN y)

end CFSG.Monster.B.TwoA.Sp8
