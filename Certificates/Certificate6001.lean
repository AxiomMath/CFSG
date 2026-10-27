module

public import CFSG.Monster.AxisCount.BabyData
public import CFSG.Monster.AxisCount.BabyCoverCheckInputs
public import CFSG.Monster.AxisCount.BabyShort
import Certificates.Kernel.AxisPlane.Baby.Assembly
import Certificates.Kernel.AxisPlane.Baby.Delta

public section

namespace Certificates

open CertificateChecks.KernelAP.Baby in
open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Baby in
theorem certificate6001 : BabyOrbits babyOrbit0
    ∧ BabyOrbits babyOrbit1
    ∧ BabyOrbits babyOrbit2
    ∧ BabyOrbits babyOrbit3
    ∧ BabyOrbits babyOrbit4
    ∧ BabyOrbits babyOrbit5
    ∧ BabyOrbits babyOrbit6
    ∧ BabyOrbits babyOrbit7
    ∧ BabyOrbits babyOrbit8
    ∧ BabyOrbits babyOrbit9
    ∧ babyDelta.ncard ≤ 46575 :=
  ⟨cover0, cover1, cover2, cover3, cover4, cover5, cover6, cover7, cover8, cover9,
    babyDelta_ncard_le⟩

end Certificates
