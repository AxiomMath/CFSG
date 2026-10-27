module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL2CertInputs
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.KL27
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.L27T
  CFSG.ComponentClassification.GrSLit.L34Facts

namespace Certificates

private theorem l27Outer_eq : l27OuterOK = outerC := by
  unfold l27OuterOK outerC
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC]
  simp only [List.all_map, List.any_map, Function.comp_def, ev_mul', ev_inv', ev_pow', one_eq_ev,
    decide_ev_eq, sift_ev]

open CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate22208 : l2OuterOK = true := by
  rw [l2OuterOK.eq_1, l27Outer_eq, kOuter, kA5Outer]
  rfl

end Certificates
