module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRank
import Certificates.Kernel.LocalQT.Base.C4131
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2Inputs

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 in
open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.J2 in
theorem certificate4131 : (RankCert.RankCertS 315 (List.range 315)
            (slpTabsA CFSG.QuasithinUnique.K1.SporadicPerm.j2ta.toArray
              CFSG.QuasithinUnique.K1.SporadicPerm.j2tb.toArray
              CFSG.QuasithinUnique.K1.SporadicPerm.j2Prog)
            CFSG.QuasithinUnique.K1.SporadicPerm.j2Qp 4
            CFSG.QuasithinUnique.K1.SporadicPerm.j2Enum.1
            CFSG.QuasithinUnique.K1.SporadicPerm.j2Enum.2.1
            CFSG.QuasithinUnique.K1.SporadicPerm.j2Enum.2.2 7) := CFSG.KD.LQT.C4131.cert

end Certificates
