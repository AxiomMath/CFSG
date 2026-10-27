module

public import CFSG.RankThree.PartOne.K1320X.CommRes
public import CFSG.RankThree.PartOne.K1320X.UThreeFive

public section

namespace CFSG.RankThree.PartOne.K1320X

open CFSG.Assembly CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K1320
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem kfCommDistinct_of_ne
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs) (h106 : K156.Full106Stmt)
    (hne : KFCommDistinctXne) : S13K.KFCommDistinct :=
  (kfCommDistinctX_of_ne hGA hS hTwo h106 hne).toKFCommDistinct

theorem kf1320UThreeAt_five_of_ne
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs) (h106 : K156.Full106Stmt)
    (h133 : S13K.KF133Two) (hne : KFCommDistinctXne)
    (hdist : RowModelsDistinct) : KF1320UThreeAt 5 :=
  kf1320UThreeAt_five hGA hS h133 (kfCommDistinctX_of_ne hGA hS hTwo h106 hne) hdist

end CFSG.RankThree.PartOne.K1320X
