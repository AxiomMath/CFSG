module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoKData
public import CFSG.Quasithin.Background.H16TwoM22Check

public section

namespace CFSG.ASVolI.AppH

open CFSG.Quasithin.H.Mathieu

@[expose] def koMats11 : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024], [1278, 1277, 228, 424, 336, 32, 64, 128, 256, 543, 1024], [990, 989, 452, 360, 176, 32, 64, 128, 256, 512, 1055], [1854, 1853, 292, 200, 496, 32, 64, 128, 256, 543, 1055], [17, 18, 24, 20, 16, 32, 64, 128, 256, 672, 1344], [1454, 1453, 248, 436, 336, 32, 64, 128, 256, 703, 1344], [878, 877, 472, 372, 176, 32, 64, 128, 256, 672, 1375], [1742, 1741, 312, 212, 496, 32, 64, 128, 256, 703, 1375], [9, 10, 24, 8, 12, 32, 64, 128, 256, 864, 1440], [1366, 1365, 248, 424, 332, 32, 64, 128, 256, 895, 1440], [694, 693, 472, 360, 172, 32, 64, 128, 256, 864, 1471], [2038, 2037, 312, 200, 492, 32, 64, 128, 256, 895, 1471], [5, 6, 4, 20, 12, 32, 64, 128, 256, 960, 1248], [1050, 1049, 228, 436, 332, 32, 64, 128, 256, 991, 1248], [538, 537, 452, 372, 172, 32, 64, 128, 256, 960, 1279], [1562, 1561, 292, 212, 492, 32, 64, 128, 256, 991, 1279]]

theorem koMats11_spec :
    koMats11 = (List.range 16).map fun t => matOf 11 (act11 (koArr t)) := by
  decide +kernel

@[expose] def D11 : KData :=
  ⟨11, koMats11, 7541891990444431387857460076772317859457515240308271577573672891569080871040855955332487748585960502635576275272111744582090926790944028147338998263578633, 6, 3,
    [(8, 8), (12, 4), (512, 2), (1024, 1), (256, 1), (128, 1), (64, 1), (32, 1), (28, 1), (3, 1)]⟩

theorem D11_chkCols : D11.chkCols = true := by decide +kernel
theorem D11_chkAb : D11.chkAb = true := by decide +kernel
theorem D11_chkLU : D11.chkLU = true := by decide +kernel
theorem D11_chkCard : D11.chkCard = true := by decide +kernel
theorem D11_chkCnt : D11.chkCnt = true := by decide +kernel
theorem D11_chkEx : D11.chkEx = true := by decide +kernel
theorem D11_chkXi : D11.chkXi = true := by decide +kernel
theorem D11_chkXb : D11.chkXb = true := by decide +kernel
theorem D11_chkTV : D11.chkTV = true := by decide +kernel
theorem D11_chkCt : D11.chkCt = true := by decide +kernel

theorem D11_good : D11.good = true := by
  simp only [KData.good, D11_chkCols, D11_chkAb, D11_chkLU, D11_chkCard, D11_chkCnt,
    D11_chkEx, D11_chkXi, D11_chkXb, D11_chkTV, D11_chkCt, Bool.and_self]

end CFSG.ASVolI.AppH
