
module

public import CFSG.Monster.Existence.TwoPoint.GammaExclTwoBCheckBase

public import CFSG.Monster.Existence.TwoPoint.GammaExclDef

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.Spin CFSG.Monster.Visible

theorem gxTwoBCheck_sound
    (h : wordLin (gxXWord ++ gxCW9) = wordLin (gxCW9 ++ gxProdWord (gxXList 9))) :
    IsConj xGriess (xHat 9) := by
  have h1 := h
  rw [wordLin_append, wordLin_append] at h1
  have h2 : fiMkW gxCW9 * xGriess = xHat 9 * fiMkW gxCW9 := by
    rw [← fiMkW_gxXWord, xHat_eq_prod, ← fiMkW_gxProdWord]
    exact Subtype.ext h1
  exact isConj_iff.2 ⟨fiMkW gxCW9, by rw [h2, mul_inv_cancel_right]⟩

end CFSG.Monster.Existence
