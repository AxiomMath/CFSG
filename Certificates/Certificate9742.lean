module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallInner
public import CFSG.GH74.KGroups.L33Inputs
import Certificates.Kernel.PermCent.KL33Glue

public section

namespace Certificates

open CFSG.GH74.KGroups in
theorem certificate9742 : ∀ t : L33.QA.originalSubgroup, orderOf t = 2 →
    CFSG.ClassicalInvolution.Q3.TA3.GoodOrInnerPred
      (L33.QP.originalSubgroup.subgroupOf L33.QA.originalSubgroup) t :=
  CFSG.Certificates.Kernel.PkCV.L33R.Glue.l33_goodOrInner

end Certificates
