module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL33Check
import CFSG.Certificates.Kernel.PermCent.SmallF3TwinSound
import Certificates.Kernel.PermCent.K8040
public import CFSG.GH74.KGroups.L33Inputs

public section

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.SmallF3T

namespace Certificates

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoL33 CFSG.GH74.KGroups in
theorem certificate8040 : fourGenCheck (elemsT L33.QA) (elemsT L33.QP) = true := by
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC, fourGenCheck_C]
  exact K8040.k8040

end Certificates
