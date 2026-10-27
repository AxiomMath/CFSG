module

public import CFSG.Milestones.ASVolI.F48.D43.Inputs
import Certificates.Kernel.D43.Cube
import Certificates.Kernel.D43.Bind
import CFSG.Certificates.Kernel.D43.KeySound

public section

open CFSG CFSG.ASVolI CFSG.KC.D43 CertificateChecks.KernelD43

namespace Certificates

open CFSG CFSG.ASVolI in
theorem certificate7801 : ∃ e : Equiv.Perm (Fin 26572), ∀ p : Fin 26572,
    ((e p : Fin 26572) : ℕ) = (burnsideF48d_phi ())[p.val]! := by
  obtain ⟨e, he⟩ := exists_perm_of_cube (F := PX.F) (k := 0) phiCube
  exact ⟨e, fun p => (he p).trans (phi_tab p.2).symm⟩

end Certificates
