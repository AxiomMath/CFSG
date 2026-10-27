module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2SigExcEnd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)


theorem s21_12aFR34F2SigExc_dataOfSetup4 {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    S21_12aFR34F2SigExc (UC6.dataOfSetup4 hS hU S)
      (Choice214U (UC6.dataOfSetup4 hS hU S)) :=
  s21_12aFR34F2SigExc_core hS hU S hMS hPart

end CFSG.LocalAnalysis.UniquenessCase.UC22
