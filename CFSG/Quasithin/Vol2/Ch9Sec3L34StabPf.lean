module

public import CFSG.Quasithin.Vol2.Ch9Sec3L34Step1
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Qrc
public import CFSG.Quasithin.Vol2.Ch9Sec3L34QSetup
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Res

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem ch9L34Stab_of
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hC58 : TheoremC58) (hD15 : D15AsPrintedSQTK)
    (hS316 : AS316SylowNonsolvable) (hKG : FactL34QuadThree) : Ch9L34Stab := by
  intro G _ _ T L I S _ H K B D hH _ hHK hKc hTK hJ hKL _ hBK hB3 hBTK hD hBD
  by_contra hns
  exact S.false_of_le_pCoreOf_l34 hC58 hD15 hS316 hKG S.q43_le S.not_isDualFFInt_l34 hH hHK hKc
    hTK hJ hKL (S.le_pCoreOf_of_not_stab h37 h38 h37c h38c rfl hH hHK hKc hTK hJ hKL hBK hB3
      hBTK hD hBD hns)

end CFSG.Quasithin.H13.Ch9
