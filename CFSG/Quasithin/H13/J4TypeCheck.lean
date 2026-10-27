module

public import CFSG.Quasithin.H13.J4Core
public meta import CFSG.Quasithin.H13.J4Core
public meta import CFSG.Quasithin.H13.J4Defs
public meta import Certificates.Data.CFSGNative.H13.J4Elems
public import CFSG.Quasithin.H13.J4TypeCheckInputs
public import Certificates.Certificate7017

public section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native

theorem w0Check_eq : w0Check = true :=
  Certificates.certificate7017.1

theorem plusChecks_eq : plusChecks = true :=
  Certificates.certificate7017.2.1

theorem genChecks_eq : genChecks = true :=
  Certificates.certificate7017.2.2.1

theorem weakChecks_eq : weakChecks = true :=
  Certificates.certificate7017.2.2.2

end CFSG.Quasithin.H13.J4
