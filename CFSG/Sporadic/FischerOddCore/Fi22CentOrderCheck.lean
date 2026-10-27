module

public import CFSG.Sporadic.FischerOddCore.Fi22Cent
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22Cent
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheckInputs
public import Certificates.Certificate2066

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer

theorem fi22CentOrder_check0 : fi22CentOrderOK 0 = true :=
  Certificates.certificate2066.1

theorem fi22CentOrder_check1 : fi22CentOrderOK 1 = true :=
  Certificates.certificate2066.2.1

theorem fi22CentOrder_check2 : fi22CentOrderOK 2 = true :=
  Certificates.certificate2066.2.2.1

theorem fi22CentOrder_check3 : fi22CentOrderOK 3 = true :=
  Certificates.certificate2066.2.2.2.1

theorem fi22CentOrder_check4 : fi22CentOrderOK 4 = true :=
  Certificates.certificate2066.2.2.2.2

end CFSG.Sporadic.FischerOddCore
