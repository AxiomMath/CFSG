module

public import Certificates.Kernel.HMathieu.Perm7119
public import Certificates.Kernel.HMathieu.T22Elems
import CFSG.Certificates.Kernel.HMathieu.PermThreeSound

public section

open CFSG.KC.HMathieu CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.MathieuLat in
theorem certificate7119 :
    inAutOK y22 = true ∧ y22[0]! = 0 ∧ y22[1]! = 1 ∧ permThreeOK T22s2 y22 = true :=
  ⟨Perm7119.aut, Perm7119.fix01.1, Perm7119.fix01.2,
    permThreeOK_of_K T22.elems_eq T22.n_size (List.all_eq_true.1 T22.vpE) Perm7119.unpk_y.symm
      Perm7119.unpk_w1.symm Perm7119.unpk_w2.symm Perm7119.vp.1 Perm7119.vp.2 Perm7119.cube
      Perm7119.ne_one Perm7119.k⟩

end Certificates
