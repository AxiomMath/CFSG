
module

public import Certificates.Data.BT2K1Vocab
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.TwoA.Base.FullCent
public import CFSG.Monster.B.TwoA.Co2Inv.Data

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv

@[expose] def b0 : LinearMap.BilinForm (ZMod 2) (Fin 8 → ZMod 2) := Matrix.toBilin' gram0

theorem b0_single (i j : Fin 8) :
    b0 (Pi.single i 1) (Pi.single j 1) = bvec 8 (gramRows.getD i 0) j := by
  rw [b0, Matrix.toBilin'_single, gram0, Matrix.of_apply]

theorem Ehat_le_Shat : Ehat ≤ Shat := Ehat_le_Jhat.trans Jhat_le_Shat

end CFSG.Monster.B.TwoA.Sp8
