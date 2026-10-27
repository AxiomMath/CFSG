module

public import Certificates.Kernel.D43.HexG
public import Certificates.Kernel.D43.HexP
public import CFSG.Certificates.Kernel.D43.TwinSound
public import CFSG.Milestones.ASVolI.F48.D43.Inputs

public section

namespace CertificateChecks.KernelD43

open CFSG.ASVolI CFSG.KC.D43

theorem gen_tab {k p : Nat} (hk : k < 8) (hp : p < 26572) :
    (burnsideF48d_gen k)[p]! = tabAt GX.F k p := by
  have h := hexTable_row GX.all (m := 511) (k := k) (p := p) (by change p < 52 * 511; omega)
    (by change 511 * k + p / 52 < 4088; omega)
  rw [← GX.eq] at h
  exact h

theorem phi_tab {p : Nat} (hp : p < 26572) : (burnsideF48d_phi ())[p]! = tabAt PX.F 0 p := by
  have h := hexTable_row PX.all (m := 511) (k := 0) (p := p) (by change p < 52 * 511; omega)
    (by change 511 * 0 + p / 52 < 511; omega)
  rw [← PX.eq] at h
  exact h

end CertificateChecks.KernelD43

end
