module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
public import CFSG.Quasithin.Vol2.KGFactRankInputs
import Certificates.Kernel.LocalQT.Base.C7145

public section

namespace Certificates

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.KGRank in
theorem certificate7145 : treeCheck m24Enum.1.size m24Qp.length m24Qp.length m24Enum.2.1 m24Enum.2.2 129 #[] = true :=
  CFSG.KD.LQT.C7145.tree

end Certificates
