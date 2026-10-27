module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
public import Certificates.Data.CFSGNative.H13.LocDblDc
public meta import Certificates.Data.CFSGNative.H13.LocDblDc
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public meta import Certificates.Data.CFSGNative.HS.Data
public import Certificates.Certificate7029
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListMain

public section

namespace CFSG.Quasithin.H13.LocDbl.HSCert

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.LocDbl.DcNative
open CFSG.Sporadic.Th.Native (ap)
open CFSG.Sporadic.HS.Native (hsData)
open CFSG.Sporadic.SmallF2 (J)

theorem hs_sylowNoDouble : SylowNoDouble ↥(J hsData) :=
  Certificates.certificate7029.1

end CFSG.Quasithin.H13.LocDbl.HSCert
