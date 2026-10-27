module

public import Certificates.Certificate589102

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.Quasithin S127 S127.I77

theorem ktSInv_holds : KtSInv :=
  Certificates.certificate589102.1

theorem ktS16_holds : KtS16 :=
  Certificates.certificate589102.2

theorem ktLine1277_holds' (h71 : Setup1271) : KtLine1277 :=
  ktLine1277_of h71 ktSInv_holds ktS16_holds

end CFSG.Quasithin.H13.I1277
