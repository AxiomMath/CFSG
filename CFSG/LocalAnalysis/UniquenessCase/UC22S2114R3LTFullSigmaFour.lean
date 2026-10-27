module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LTFullSigmaCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)


theorem s21_14R3LTFullSigma_dataOfSetup4 {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    S21_14R3LTFullSigma (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) := by
  rintro hH c L hL hX hpow f hshape hk hodd hn3 hBT hBL hfaith hML hfull
    r hr hr7 hrn hrf hrf' hrσ hcent
  exact (s21_14R3LT_full_sigma_core hS hU S hMS hPart hH c L hL hX hpow
    f hshape hk hodd hn3 hBT hBL hfaith hML hfull r hr hr7 hrn hrf hrf' hrσ hcent).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
