module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)


theorem s21_12aFR34F2Even2_dataOfSetup4 {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    S21_12aFR34F2Even2 (UC6.dataOfSetup4 hS hU S) (Choice214U (UC6.dataOfSetup4 hS hU S)) :=
  s21_12aFR34F2Even2_dataOfSetup4_of_exc hS hU S hMS hPart

end CFSG.LocalAnalysis.UniquenessCase.UC22
