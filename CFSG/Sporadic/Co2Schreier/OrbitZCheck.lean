module

public import CFSG.Sporadic.Co2Schreier.OrbitCheck
public meta import CFSG.Sporadic.Co2Schreier.OrbitCheck
public import Certificates.Certificate2055

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Sporadic.Schreier.Co3

theorem izList_length : izList.length = 284 :=
  Certificates.certificate2055.1

theorem orbitZ_check :
    orbitRecordOK izList 56925 (co3KeySearch aArrs izList 56925) = true :=
  Certificates.certificate2055.2

end CFSG.Sporadic.Co2Schreier
