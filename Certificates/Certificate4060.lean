module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRank
import Certificates.Kernel.LocalQT.Base.C4060
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHSInputs

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 in
open CFSG.Open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 in
open CFSG.Blueprint.NativeSporadic (Carrier) in
open CFSG.Sporadic.HS.Native (hsData) in
theorem certificate4060 : (RankCert.RankCertS hsData.n hsB (slpTabsA hsTa hsTb hsProg) hsQp 4 hsEnum.1 hsEnum.2.1
            hsEnum.2.2 9) :=
  CFSG.KD.LQT.C4060.cert

end Certificates
