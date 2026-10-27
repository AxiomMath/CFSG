module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRuInputs
public import CFSG.Quasithin.Vol2.KGFactRankRuData
import Certificates.Kernel.LocalQT.Base.C7147

public section

namespace Certificates

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.KGRank in
theorem certificate7147 :
    treeCheck ruEnum.1.size ruQp.length ruQp.length ruEnum.2.1 ruEnum.2.2 338 ruRankNodes = true := CFSG.KD.LQT.C7147.tree

end Certificates
