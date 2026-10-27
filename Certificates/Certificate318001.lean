module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRank
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKHS
public import CFSG.Sporadic.HS.Group
public import Certificates.Data.CFSGNative.HS.Data

public section

namespace Certificates

open CFSG.QuasithinUnique.Lin2 CFSG.Sporadic.SmallF2 in
theorem certificate318001 : RankCert.ElemAbelianLt ↥(J CFSG.Sporadic.HS.Native.hsData) 32 :=
  CFSG.QuasithinUnique.Lin2.hs_group_rank

end Certificates
