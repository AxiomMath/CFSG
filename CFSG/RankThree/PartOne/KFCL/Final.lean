module

public import CFSG.RankThree.PartOne.KFCL.Row1
public import CFSG.RankThree.PartOne.KFCL.Row2
public import CFSG.RankThree.PartOne.KFCL.At
public import CFSG.RankThree.PartOne.K159H.Chain

public section

namespace CFSG.RankThree.PartOne.KFCL

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem kfCompLayer_of_rootModels (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hS13 : Sec13Avail) (hEI : Sec1511.KFEI)
    (hAt : KFAtEven) (h3 : RootModelRow 3) (h4 : RootModelRow 4) : K159.KFCompLayer :=
  K159.kfCompLayer_of_gen hS h82 hS13 hAt
    (kfCompGenEven_of_rows (kfCompGenRow_one hEI (hAt 1 le_rfl (by norm_num)))
      (kfCompGenRow_two hEI (hAt 2 (by norm_num) (by norm_num)))
      (kfCompGenRow_of_rootModel (by norm_num) (by norm_num) hEI (hAt 3 (by norm_num) (by norm_num)) h3)
      (kfCompGenRow_of_rootModel (by norm_num) (by norm_num) hEI (hAt 4 (by norm_num) le_rfl) h4))

theorem kfCompLayer_of_allSplit (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hS13 : Sec13Avail) (hEI : Sec1511.KFEI)
    (hAll : S15K.KF158AllSplit) (hAt4 : KFAtRow 4) (h3 : RootModelRow 3) (h4 : RootModelRow 4) :
    K159.KFCompLayer :=
  kfCompLayer_of_rootModels hS h82 hS13 hEI (kfAtEven_of_allSplit hAll hAt4) h3 h4

end CFSG.RankThree.PartOne.KFCL
