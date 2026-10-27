module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowMathieu
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowJ1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowJ2M
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowJ3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowJ4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowMcL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHeM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowRu
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowSuz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowCo1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowCo2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowCo3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHN
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowTh
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowLy

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

theorem w4Thm11_1RowM4_table_of_five
    (hFi22 : W4Thm11_1RowM4 .Fi22) (hFi23 : W4Thm11_1RowM4 .Fi23)
    (hFi24 : W4Thm11_1RowM4 .Fi24Prime) (hB : W4Thm11_1RowM4 .B) (hM : W4Thm11_1RowM4 .M) :
    ∀ s : TauCeti.SporadicName, s ≠ .M22 → W4Thm11_1RowM4 s := by
  intro s hs
  cases s with
  | M11 => exact w4Thm11_1RowM_M11_holds.rowM4 (by decide)
  | M12 => exact w4Thm11_1RowM_M12_holds.rowM4 (by decide)
  | M22 => exact absurd rfl hs
  | M23 => exact w4Thm11_1RowM_M23_holds.rowM4 (by decide)
  | M24 => exact w4Thm11_1RowM_M24_holds.rowM4 (by decide)
  | J1 => exact w4Thm11_1Row_J1_holds.rowM.rowM4 (by decide)
  | J2 => exact w4Thm11_1RowM_J2_holds.rowM4 (by decide)
  | J3 => exact w4Thm11_1RowM_J3_holds.rowM4 (by decide)
  | J4 => exact w4Thm11_1RowM_J4_holds.rowM4 (by decide)
  | HS => exact w4Thm11_1RowM_HS_holds.rowM4 (by decide)
  | McL => exact w4Thm11_1RowM_McL_holds.rowM4 (by decide)
  | He => exact w4Thm11_1RowM_He_holds.rowM4 (by decide)
  | Ru => exact w4Thm11_1Row_Ru_holds.rowM.rowM4 (by decide)
  | Suz => exact w4Thm11_1RowM_Suz_holds.rowM4 (by decide)
  | ONan => exact w4Thm11_1RowM_ONan_holds.rowM4 (by decide)
  | Co1 => exact w4Thm11_1RowM_Co1_holds.rowM4 (by decide)
  | Co2 => exact w4Thm11_1RowM_Co2_holds.rowM4 (by decide)
  | Co3 => exact w4Thm11_1RowM_Co3_holds.rowM4 (by decide)
  | Fi22 => exact hFi22
  | Fi23 => exact hFi23
  | Fi24Prime => exact hFi24
  | HN => exact w4Thm11_1RowM4_HN_holds
  | Th => exact w4Thm11_1RowM_Th_holds.rowM4 (by decide)
  | B => exact hB
  | M => exact hM
  | Ly => exact w4Thm11_1RowM_Ly_holds.rowM4 (by decide)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
