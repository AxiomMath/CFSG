module

public import Certificates.Kernel.HMathieu.Perm7120
public import Certificates.Kernel.HMathieu.T12Elems
import CFSG.Certificates.Kernel.HMathieu.PermThreeSound

public section

open CFSG.KC.HMathieu CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12 CFSG.Quasithin.H.MathieuLat in
theorem certificate7120 :
    inAutOK y12 = true ∧ okPair y12 (invArr y12) = true ∧ permThreeOK T12s2 y12 = true :=
  ⟨Perm7120.aut, Perm7120.pair,
    permThreeOK_of_K T12.elems_eq T12.n_size (List.all_eq_true.1 T12.vpE) Perm7120.unpk_y.symm
      Perm7120.unpk_w1.symm Perm7120.unpk_w2.symm Perm7120.vp.1 Perm7120.vp.2 Perm7120.cube
      Perm7120.ne_one Perm7120.k⟩

end Certificates
