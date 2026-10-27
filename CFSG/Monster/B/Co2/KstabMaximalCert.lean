module

public import Certificates.Certificate10027

public section

namespace CFSG.Monster.B.Co2

open CFSG.Monster.Existence.CoPair.Native CFSG.KC.AxisPlane

theorem kstabOrbit_one :
    orbitOf 2 genXY 1 ⊆ Set.Iio (2 ^ 24) ∧ (orbitOf 2 genXY 1).ncard = 47104 :=
  Certificates.certificate10027.1

theorem kstabOrbit_sixtyFour :
    orbitOf 2 genXY 64 ⊆ Set.Iio (2 ^ 24) ∧ (orbitOf 2 genXY 64).ncard = 46575 :=
  Certificates.certificate10027.2.1

theorem kstabOrbit_fourThousand :
    orbitOf 2 genXY 4096 ⊆ Set.Iio (2 ^ 24) ∧ (orbitOf 2 genXY 4096).ncard = 4600 :=
  Certificates.certificate10027.2.2

end CFSG.Monster.B.Co2
