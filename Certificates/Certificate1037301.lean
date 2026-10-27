module

public import Certificates.Data.W4Fi22OuterGen
import Certificates.Kernel.LocalQT.Tc.C1037301
import CFSG.Certificates.Kernel.LocalQTTcKSound

public section

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

namespace Certificates

open CertificateChecks

open CertificateChecks.KD.LQT.C1037301 in
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row in
theorem certificate1037301 : fi22OuterGenCheck () = true := by
  unfold fi22OuterGenCheck
  rw [gens_eq, t_eq, targ_eq]
  exact CFSG.KC.LQT.TCK.tcK_sound hT

end Certificates
