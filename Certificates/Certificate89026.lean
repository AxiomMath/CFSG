module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SF4Data
import Certificates.Kernel.AlphaMc.HermSp
import CFSG.Certificates.Kernel.AlphaAltSpSound

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.R3 CFSG.LocalAnalysis.GLTheoremA.F4Sym

theorem certificate89026 : CFSG.LocalAnalysis.GLTheoremA.F4Sym.f4Check () = true := by
  unfold f4Check
  rw [KernelAM.f4F_K, Bool.true_and]
  exact altOK_of_altSp (n := 10) (T := f4CiSupp) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    KernelAM.f4A_K

end Certificates
