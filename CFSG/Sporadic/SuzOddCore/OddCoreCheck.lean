module

public import CFSG.Sporadic.SuzOddCore.InvTCheck
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Sporadic.SuzOddCore.InvTCheck
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public import CFSG.Sporadic.SuzOddCore.OddCoreCheckInputs
public import Certificates.Certificate2303

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native

theorem oddEntry_check0 : oddEntryOK 0 = true :=
  Certificates.certificate2303.1

theorem oddEntry_check1 : oddEntryOK 1 = true :=
  Certificates.certificate2303.2.1

theorem oddEntry_check2 : oddEntryOK 2 = true :=
  Certificates.certificate2303.2.2.1

theorem oddEntry_check3 : oddEntryOK 3 = true :=
  Certificates.certificate2303.2.2.2

end CFSG.Sporadic.SuzOddCore
