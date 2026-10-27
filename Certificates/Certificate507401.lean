module

public import Certificates.Data.E4Sp6TwinLay
import CFSG.Certificates.Kernel.PermCent.Sp6BSound
import Certificates.Kernel.PermCent.K507401
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.ClassicalInvolution.Q3.TL4.E4Sp6 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.Sp6B

namespace Certificates

open CertificateChecks

private theorem twinLay_eq507401 : twinLayCheck () = twinLayC := by
  rw [twinLayCheck.eq_1, L0_ev, L1_ev, ws_ev, enum_ev, map_tab, twinLayC.eq_1, layC.eq_1]
  simp only [List.filter_map, List.all_map, List.any_map, List.length_map, Function.comp_def,
    getD_ev, memberElems_ev, commAll_ev, ordThree_ev, ev_mul', ev_inv', one_eq_ev, decide_ev_eq]

theorem certificate507401 : CFSG.ClassicalInvolution.Q3.TL4.E4Sp6.twinLayCheck () = true := by
  rw [twinLay_eq507401]
  exact KernelPermCent.k507401

end Certificates
