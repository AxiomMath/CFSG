module

public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22Data
public import CFSG.Sporadic.FischerOddCore.Fi24R2KCheck
public import CFSG.Sporadic.FischerOddCore.Fi22Cent
public meta import CFSG.Sporadic.FischerOddCore.FischerOuterFi22Data
public meta import CFSG.Sporadic.FischerOddCore.Fi24R2KCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22Cent
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs
public import Certificates.Certificate2079

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem fo22N3Chain_ok :
    fo22ChainOK 3510 fo22N3Strong #[9, 0, 1, 2] fo22N3Words 2 7 174182400 = true :=
  Certificates.certificate2079.1

theorem fo22P3Chain_ok :
    fo22ChainOK 1575 fo22P3Strong #[0, 1, 2, 4, 3] fo22P3Words 2 11 174182400 = true :=
  Certificates.certificate2079.2.1

theorem fo22N4Chain_ok :
    fo22ChainOK 3510 fo22N4Strong #[0, 1, 2] fo22N4Words 2 7 1451520 = true :=
  Certificates.certificate2079.2.2.1

theorem fo22P4Chain_ok :
    fo22ChainOK 63 fo22P4Strong #[0, 1, 2, 4, 3, 5] fo22P4Words 2 11 1451520 = true :=
  Certificates.certificate2079.2.2.2.1

theorem fo22P2Chain_ok :
    fo22ChainOK 27 fo22P2Strong #[0, 1, 2, 3, 5, 7] fo22P2Words 3 11 51840 = true :=
  Certificates.certificate2079.2.2.2.2.1

theorem fo22N3InNormal_ok :
    fo22InNormalOK fo22N3Strong #[9, 0, 1, 2] (fi22CentStrong 3)
      ((fi22CentStrong 3).extract 0 9) = true :=
  Certificates.certificate2079.2.2.2.2.2.1

theorem fo22N4InNormal_ok :
    fo22InNormalOK fo22N4Strong #[0, 1, 2] (fi22CentStrong 4)
      ((fi22CentStrong 4).extract 0 9) = true :=
  Certificates.certificate2079.2.2.2.2.2.2.1

theorem fo22Class3_ok : fo22ClassOK fo22N3Strong fo22S03 fo22Tree3 fo22P3Strong 1575 = true :=
  Certificates.certificate2079.2.2.2.2.2.2.2.1

theorem fo22Orbit4_ok : fo22OrbitOK fo22N4Strong fo22O63 fo22P4Strong 63 = true :=
  Certificates.certificate2079.2.2.2.2.2.2.2.2.1

theorem fo22Tree3_ok : fo22TreeOK 1575 fo22P3Strong fo22TOrd3 fo22TPa3 fo22TGe3 = true :=
  Certificates.certificate2079.2.2.2.2.2.2.2.2.2.1

theorem fo22Tree4_ok : fo22TreeOK 63 fo22P4Strong fo22TOrd4 fo22TPa4 fo22TGe4 = true :=
  Certificates.certificate2079.2.2.2.2.2.2.2.2.2.2.1

theorem fo22Sub3_ok :
    fo22SubOK 1575 fo22P3Strong fo22Lab3 fo22Ord3 fo22TPar3 fo22TGen3 fo22Start3 7 = true :=
  Certificates.certificate2079.2.2.2.2.2.2.2.2.2.2.2.1

theorem fo22Sub4_ok :
    fo22SubOK 63 fo22P4Strong fo22Lab4 fo22Ord4 fo22TPar4 fo22TGen4 fo22Start4 3 = true :=
  Certificates.certificate2079.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem fo22Order3_ok : fo22OrderOK 1575 fo22P3Strong 3 5 0 7 = true :=
  Certificates.certificate2079.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem fo22Order4_ok : fo22OrderOK 63 fo22P4Strong 3 2 2 7 = true :=
  Certificates.certificate2079.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem fo22H2_ok :
    fo22H2OK (fi22CentStrong 2) ((fi22CentStrong 2).extract 0 3) fo22S02 fo22Tree2
      fo22P2Strong = true :=
  Certificates.certificate2079.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.FischerOddCore
