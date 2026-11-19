
module

public import CFSG.Monster.Existence.TwoPoint.GammaExclTwoBData
public import CFSG.Monster.Existence.TwoPoint.GammaExclDefBase

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.Spin CFSG.Monster.Visible

def gxXWord : List Native.Gen := [.rho (true, 0, 0)]

theorem wordLin_gxXWord : wordLin gxXWord = xmat := by
  have h : Rep4371.pauliQ (true, 0, 0) = zQ := by
    unfold Rep4371.pauliQ zQ
    congr 1
    simp [Rep4371.toSC, SpinCoord.z, Rep4371.boolZ, Rep4371.toC_zero, Rep4371.toD_zero]
  show wordLin [Native.Gen.rho (true, 0, 0)] = xmat
  rw [wordLin_cons, wordLin_nil, one_mul, Native.Gen.toLin_rho, h, rhoEquiv_zQ, xmat_eq_xB]

theorem fiMkW_gxXWord : fiMkW gxXWord = xGriess := Subtype.ext wordLin_gxXWord

@[noinline] def gxTwoBCheck : Bool :=
  (gxXWord ++ gxCW9 ++ (gxCW9 ++ gxProdWord (gxXList 9))).all Native.Gen.validB &&
    checkP4 (HS.pw gxXWord ++ HS.pw gxCW9) (HS.pw gxCW9 ++ gxProdP (gxXList 9))

end CFSG.Monster.Existence
