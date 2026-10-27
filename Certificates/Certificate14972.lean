module

public import CFSG.RankThree.PartOne.KE6.E8T3SevenInputs
import CFSG.Certificates.Kernel.E8Seven.Sound
import Certificates.Kernel.E8Seven.Checks

open CFSG.RankThree.PartOne.KE6 CFSG.Blueprint.Chevalley Certificates.E8Seven

namespace CertificateChecks.Batch14972

open CFSG.RankThree.PartOne.KE6 CFSG.Blueprint.Chevalley Certificates.E8Seven

open CertificateChecks.E8SevenK

theorem t2_eq : CFSG.KD.E8Seven.t2 = e8ArtifactRoots.map code2 := by decide +kernel

theorem t4_eq : CFSG.KD.E8Seven.t4 = e8ArtifactRoots.map code4 := by decide +kernel

theorem chk2 : ∀ a < 7, K.chk CFSG.KD.E8Seven.t2 a = true := by
  intro a ha
  interval_cases a
  exacts [c14972e20, c14972e21, c14972e22, c14972e23, c14972e24, c14972e25, c14972e26]

theorem chk4 : ∀ a < 7, K.chk CFSG.KD.E8Seven.t4 a = true := by
  intro a ha
  interval_cases a
  exacts [c14972e40, c14972e41, c14972e42, c14972e43, c14972e44, c14972e45, c14972e46]

end CertificateChecks.Batch14972

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne.KE6 in
theorem certificate14972 : E8SevenCount :=
  e8SevenCount_of CertificateChecks.Batch14972.t2_eq CertificateChecks.Batch14972.t4_eq CertificateChecks.Batch14972.chk2 CertificateChecks.Batch14972.chk4

end Certificates
