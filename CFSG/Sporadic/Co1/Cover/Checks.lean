module

public import CFSG.Sporadic.Co1.Cover.Data
public import Certificates.Certificate10061
public meta import CFSG.Sporadic.Co1.Cover.Data
public meta import CFSG.Sporadic.Co1.Module.OddProg
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Sporadic.Co1.Module.OddNative
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Odd
public meta import Certificates.Data.CFSGNative.Co1.CoverCheck
public import CFSG.Sporadic.Co1.Module.InvDataBase
public import CFSG.Sporadic.Co1.Module.InvRepsBase
public meta import CFSG.Sporadic.Co1.Module.InvRepsBase

public section

set_option Elab.async false

namespace CFSG.Sporadic.Co1.Cover

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.CoverNative

theorem cov_basic : epsBasicOK epsRows = true :=
  Certificates.certificate10061.2.1

theorem cov_inj : epsInjOK epsRows = true :=
  Certificates.certificate10061.2.2.1

theorem cov_norm_a :
    normOK epsRows (rrCov 4) (transposeRows 11 Aa) = true :=
  Certificates.certificate10061.2.2.2.1

theorem cov_norm_b :
    normOK epsRows (rrCov 5) (transposeRows 11 Ba) = true :=
  Certificates.certificate10061.2.2.2.2.1

theorem cov_t0_order : orderIs t0Rows 2 = true :=
  Certificates.certificate10061.2.2.2.2.2.1

theorem cov_t0_counts :
    CFSG.Sporadic.Co1.Module.countsOK t0Rows 4096 0 = true :=
  Certificates.certificate10061.2.2.2.2.2.2

end CFSG.Sporadic.Co1.Cover
