module

public import CFSG.Monster.GMS.ASegAmalgamAssemble
public import CFSG.Monster.GMS.ASegSimple
public import CFSG.Monster.GMS.ASegConnH87
public import CFSG.Monster.GMS.ASegTwoA
public import CFSG.Monster.GMS.CoTwoAutMain
public import CFSG.Monster.GMS.InterfacesOf
public import CFSG.Sporadic.Co1.Cover.Final
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3024
public import Certificates.Certificate3115
public import Certificates.Certificate3117
public import Certificates.Certificate9123
public import Certificates.Certificate9215
public import Certificates.Certificate9251
public import Certificates.Certificate9252
public import Certificates.Certificate9253
public import Certificates.Certificate9254
public import Certificates.Certificate9255
public import Certificates.Certificate9256
public import Certificates.Certificate9257
public import Certificates.Certificate9258
public import Certificates.Certificate9259
public import Certificates.Certificate9260
public import Certificates.Certificate9261
public import Certificates.Certificate9262
public import Certificates.Certificate9263
public import Certificates.Certificate9264
public import Certificates.Certificate9265
public import Certificates.Certificate9266
public import Certificates.Certificate10028
public import Certificates.Certificate10029
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10037
public import Certificates.Certificate10038
public import Certificates.Certificate10039
public import Certificates.Certificate10040
public import Certificates.Certificate10041
public import Certificates.Certificate10042
public import Certificates.Certificate10043
public import Certificates.Certificate10044
public import Certificates.Certificate10045
public import Certificates.Certificate10060
public import Certificates.Certificate10061
public import Certificates.Certificate10062
public import Certificates.Certificate10063
public import Certificates.Certificate10064
public import Certificates.Certificate10065
public import Certificates.Certificate10066
public import Certificates.Certificate10067
public import Certificates.Certificate10068
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate10072
public import Certificates.Certificate10073
public import Certificates.Certificate10074
public import Certificates.Certificate10075
public import Certificates.Certificate10076
public import Certificates.Certificate10077
public import Certificates.Certificate10079
public import Certificates.Certificate9250
public import Certificates.Certificate9267
public import Certificates.Certificate8955
public import CFSG.Monster.GMS.BabyReduce

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Recog

structure ASegLiterature : Prop where
  tableV : TableVStatement
  tableIII : BabyTableIII
  tableIV : BabyTableIV
  threeSwap : BabyThreeSwap
  twoBabyUnique : TwoBabyUnique
  twoAAutInner : BabyTwoAAutInner

theorem ASegLiterature.interfaces
    {d₀ : B} (L : ASegLiterature) (hS : SLSStatement d₀)
    (G : Type) [Group G] [Finite G] : GMSInterfaces d₀ G :=
  .of_babyFacts hS L.tableV.inG L.tableIII L.tableIV L.threeSwap

theorem nonempty_mulEquiv_of_aseg_simple
    {G G' : Type} [Group G] [Group G'] [Finite G]
    [Finite G'] {d₀ d₀' : B} (L : ASegLiterature) (hS : SLSStatement d₀)
    (hS' : SLSStatement d₀') {a z₀ : G} {a' z₀' : G'} (hG : GMSF1Type d₀ a z₀)
    (hG' : GMSF1Type d₀' a' z₀') (hΓ' : Triangulable (twoAGraph a'))
    (hsimple : IsSimpleGroup G') : Nonempty (G ≃* G') := by
  have I : GMSInterfaces d₀ G := L.interfaces hS G
  have I' : GMSInterfaces d₀' G' := L.interfaces hS' G'
  exact nonempty_mulEquiv_of_triangulable_simple I I' hG hG' L.twoBabyUnique
    CFSG.Sporadic.Co1.Cover.co1DoubleCoverTwoB
    (twoAGraph_preconnected I hG) (twoAGraph_preconnected I' hG') hΓ' hsimple
    (kAutRigid_of_twoA I hG (centInvAutInnerTwoA_of_baby I hG L.twoAAutInner))
    (centInvAutInnerTwoAB_of I hG)

end CFSG.Monster.GMS
