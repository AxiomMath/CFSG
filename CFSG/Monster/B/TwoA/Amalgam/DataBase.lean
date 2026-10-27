
module

public import CFSG.Monster.B.Classical.ThreePlaneData
public import CFSG.Monster.B.TwoA.Unitary.Form
public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Data.BT2K1Vocab

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

@[expose] def e6 (k : Fin 6) : Unitary.V6 := Pi.single k 1

@[expose] def Tsp : Submodule CFSG.Fischer.F4 Unitary.V6 :=
  Submodule.span CFSG.Fischer.F4 {e6 0, e6 1, e6 2}

@[expose] def Hsp : Submodule CFSG.Fischer.F4 Unitary.V6 :=
  Submodule.span CFSG.Fischer.F4 {e6 1, e6 2}

@[expose] def Rsp : Submodule CFSG.Fischer.F4 Unitary.V6 :=
  Submodule.span CFSG.Fischer.F4 {e6 2}

theorem vec100_ne_zero : (![1, 0, 0] : Fin 3 → CFSG.Fischer.F4) ≠ 0 := by
  intro h
  have := congrFun h 0
  exact one_ne_zero this

@[expose] def pPt : Classical.ThreePlane.PlanePoint :=
  Projectivization.mk CFSG.Fischer.F4 ![1, 0, 0] vec100_ne_zero

@[expose] def ellLine : Set Classical.ThreePlane.PlanePoint :=
  {x | ∃ (a b : CFSG.Fischer.F4) (h : (![a, b, 0] : Fin 3 → CFSG.Fischer.F4) ≠ 0),
    x = Projectivization.mk CFSG.Fischer.F4 ![a, b, 0] h}

end CFSG.Monster.B.TwoA.Amalgam
