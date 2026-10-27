module

public import CFSG.Sporadic.Co2Schreier.OrbitCheck
public meta import CFSG.Sporadic.Co2Schreier.OrbitCheck
public import Certificates.Certificate2054

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Sporadic.Schreier.Co3

theorem itList_length : itList.length = 140 :=
  Certificates.certificate2054.1

theorem orbitT_check :
    orbitRecordOK itList 1024650 (co3KeySearch aArrs itList 1024650) = true :=
  Certificates.certificate2054.2

end CFSG.Sporadic.Co2Schreier
