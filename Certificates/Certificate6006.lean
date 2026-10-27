module

public import CFSG.Monster.AxisCount.CoverCheckInputs
import Certificates.Kernel.AxisPlane.Cover.Assembly

public section

namespace Certificates

open CertificateChecks.KernelAP.Cover in
open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Cert in
theorem certificate6006 : CoverOrbits 0
    ∧ CoverOrbits 1
    ∧ CoverOrbits 2
    ∧ CoverOrbits 3
    ∧ CoverOrbits 4
    ∧ CoverOrbits 5
    ∧ CoverOrbits 6
    ∧ CoverOrbits 7
    ∧ CoverOrbits 8
    ∧ CoverOrbits 9
    ∧ CoverOrbits 10
    ∧ CoverOrbits 11 :=
  ⟨cover0, cover1, cover2, cover3, cover4, cover5, cover6, cover7, cover8, cover9, cover10,
    cover11⟩

end Certificates
