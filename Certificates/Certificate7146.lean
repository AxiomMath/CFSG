module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHeInputs
public import CFSG.Quasithin.Vol2.KGFactRankInputs
import Certificates.Kernel.LocalQT.Base.C7146

public section

namespace Certificates

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.KGRank in
theorem certificate7146 : treeCheck heEnum.1.size heQp.length heQp.length heEnum.2.1 heEnum.2.2 5 #[] = true :=
  CFSG.KD.LQT.C7146.tree

end Certificates
