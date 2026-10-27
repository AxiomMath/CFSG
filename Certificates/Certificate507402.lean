module

public import Certificates.Data.E4Sp6TwinPerf
import CFSG.Certificates.Kernel.PermCent.Sp6BSound
import Certificates.Kernel.PermCent.K507402
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.ClassicalInvolution.Q3.TL4.E4Sp6 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.Sp6B

namespace Certificates

open CertificateChecks

private theorem twinPerf_eq507402 : twinPerfCheck () = twinPerfC := by
  rw [twinPerfCheck.eq_1, L0_ev, L1_ev, ws_ev, enum_ev, map_tab, twinPerfC.eq_1, layC.eq_1]
  simp only [List.filter_map, List.all_map, List.any_map, List.length_map, List.isEmpty_map,
    Function.comp_def, getD_ev, memberElems_ev, commAll_ev, ordThree_ev, ev_mul', ev_inv',
    one_eq_ev, decide_ev_eq]

theorem certificate507402 : CFSG.ClassicalInvolution.Q3.TL4.E4Sp6.twinPerfCheck () = true := by
  rw [twinPerf_eq507402]
  exact KernelPermCent.k507402

end Certificates
