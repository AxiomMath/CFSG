module

public import CFSG.RankThree.PartOne.S15K.CovFive

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def KF158FiveModel : Prop := KF158FiveRefl ∧ KF158FiveS

theorem kf158AFive_of_five (hS : SchreierFor InCatalog) (h82 : LocalThetaComponentEmbeddingFrontier)
    (hPair : KFU5PairEx) (hM : KF158FiveModel) : KF158AFive :=
  kf158AFive_of_model hS h82 hPair hM.1 hM.2

theorem kf158CovAtRowFive_of_five (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hPair : KFU5PairEx)
    (hM : KF158FiveModel) (h156 : KF156') : KF158CovAtRowFive :=
  kf158CovAtRowFive_of_model hS h82 hPair hM.2 h156

end CFSG.RankThree.PartOne.S15K
