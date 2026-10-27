
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsBase
public import Certificates.Data.CFSGNative.MonsterB.Sp8Check
public meta import Certificates.Data.CFSGNative.MonsterB.Sp8Check
public meta import CFSG.Monster.B.Rep4371.GlueDefs
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.Lifts CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.Xi Matrix

@[expose] def gDiff (k : ℕ) : Model.Pauli := genDiff.getD k (false, 0, 0)

@[expose] def permFs (eP : Array ℕ → Bool → ℕ → Bool × Bool × ℕ)
    (eQ : Model.Pauli → Bool → ℕ → Bool × Bool × ℕ) (kap : Array ℕ → ℕ → Bool) (j : ℕ) :
    List (Bool → ℕ → Bool × Bool × ℕ) :=
  [eP fPerms[j]!, eQ (false, 0, if kap fPerms[j]! 63 then 62 else 0)]

@[expose] def signFs (eY : ℕ → Bool → ℕ → Bool × Bool × ℕ) (j : ℕ) :
    List (Bool → ℕ → Bool × Bool × ℕ) :=
  (signCodesOf j).map eY

end CFSG.Monster.B.TwoA.Sp8
