module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuCertificate
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SporLat.Build
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuInputs
import Certificates.Kernel.LocalQT.Quot.F4080
import Certificates.Kernel.LocalQT.Quot.C4080H
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.Ru in
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 in
open CFSG.Sporadic.Ru.Native (ruData) in
open CFSG.Open (pCoreOf) in
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert in
theorem certificate4080 : (QuotOK ruData.n ruB ruQuotL1 ruQuot1 ruQuotEnum.1 ruQuotEnum.2.1 ruQuotEnum.2.2 122880) := CFSG.KD.LQT.C4080.quot_cert

end Certificates

end
