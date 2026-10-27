module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SU6Data
import Certificates.Kernel.AlphaMc.HermSp
import CFSG.Certificates.Kernel.AlphaAltSpSound

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.R3 CFSG.LocalAnalysis.GLTheoremA.U6Herm

theorem certificate89025 : CFSG.LocalAnalysis.GLTheoremA.U6Herm.u6Check () = true := by
  unfold u6Check
  rw [KernelAM.u6F_K, Bool.true_and]
  exact altOK_of_altSp (n := 9) (T := u6CiSupp) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    KernelAM.u6A_K

end Certificates
