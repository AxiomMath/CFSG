module

public import CFSG.RankThree.PartOne.KEXC.ScalarAssemble
public import CFSG.RankThree.PartOne.KFOUT3.G2Aut

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU


theorem kf1215Scalar2 : KF1215Scalar 2 := by
  intro G _ _ p A c L E ctx hmodel n hn
  have hcore := ctx.table_core
  refine exists_scalar_of_weyl_scalar ctx hn fun y hyL hyF => ?_
  exact KFOUT3.exists_weyl_scalar hcore.prime hcore.five_le hcore.center_pPrime hcore.F_le
    hcore.F_exp hcore.F_comm hcore.maximal hmodel hyL hyF

end CFSG.RankThree.PartOne.KEXC
