module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoKData
public import CFSG.Quasithin.Background.H16TwoM22Check

public section

namespace CFSG.ASVolI.AppH

open CFSG.Quasithin.H.Mathieu

@[expose] def koMats10 : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32, 64, 128, 256, 512], [593, 114, 212, 168, 16, 32, 64, 128, 288, 512], [449, 226, 180, 88, 16, 32, 64, 128, 256, 544], [945, 146, 100, 248, 16, 32, 64, 128, 288, 544], [9, 12, 10, 8, 16, 32, 64, 128, 336, 672], [761, 124, 218, 168, 16, 32, 64, 128, 368, 672], [409, 236, 186, 88, 16, 32, 64, 128, 336, 640], [841, 156, 106, 248, 16, 32, 64, 128, 368, 640], [5, 12, 4, 6, 16, 32, 64, 128, 432, 720], [645, 124, 212, 166, 16, 32, 64, 128, 400, 720], [373, 236, 180, 86, 16, 32, 64, 128, 432, 752], [981, 156, 100, 246, 16, 32, 64, 128, 400, 752], [3, 2, 10, 6, 16, 32, 64, 128, 480, 624], [547, 114, 218, 166, 16, 32, 64, 128, 448, 624], [291, 226, 186, 86, 16, 32, 64, 128, 480, 592], [803, 146, 106, 246, 16, 32, 64, 128, 448, 592]]

theorem koMats10_spec :
    koMats10 = (List.range 16).map fun t => matOf 10 (act10 (koArr t)) := by
  decide +kernel

@[expose] def D10 : KData :=
  ⟨10, koMats10, 28950230901860469398263684891544233923488650320386368227458800854042216054785, 5, 1,
    [(4, 8), (6, 4), (256, 2), (512, 1), (128, 1), (64, 1), (32, 1), (16, 1), (14, 1)]⟩

theorem D10_chkCols : D10.chkCols = true := by decide +kernel
theorem D10_chkAb : D10.chkAb = true := by decide +kernel
theorem D10_chkLU : D10.chkLU = true := by decide +kernel
theorem D10_chkCard : D10.chkCard = true := by decide +kernel
theorem D10_chkCnt : D10.chkCnt = true := by decide +kernel
theorem D10_chkEx : D10.chkEx = true := by decide +kernel
theorem D10_chkXi : D10.chkXi = true := by decide +kernel
theorem D10_chkXb : D10.chkXb = true := by decide +kernel
theorem D10_chkTV : D10.chkTV = true := by decide +kernel
theorem D10_chkCt : D10.chkCt = true := by decide +kernel

theorem D10_good : D10.good = true := by
  simp only [KData.good, D10_chkCols, D10_chkAb, D10_chkLU, D10_chkCard, D10_chkCnt,
    D10_chkEx, D10_chkXi, D10_chkXb, D10_chkTV, D10_chkCt, Bool.and_self]

end CFSG.ASVolI.AppH
